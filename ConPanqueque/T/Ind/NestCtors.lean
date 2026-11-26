import ConPanqueque.T.Ind.CtorChecks

/-!
# `nestCtors` at the root frame: every constructor of one member through the positivity walk

The state's constructor records (`ns.ctorNfs`) and the outputs (`(kinds, closed)` pairs) are pointer blocks, appended
to; `ns.keys`/`ns.active` stay empty (no container frame).  Checks that fail in the twin hang here.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

section
variable {σ : Type}

/-- **`whnf` at the checker's fuel, by the port**. -/
theorem whnfTop (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx}
    (hok : CtxOK C) (hc : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hs : C.side = false) (s : AState)
    (d : Nat) (hd : d < 2 ^ 63) (e : EIdx) :
    Callee (σ := σ) C kParams [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s
      (whnf mode C.fe checkFuel d e) (PostK C) := by
  have : whnf mode C.fe checkFuel d e = (knot mode C checkFuel).whnf d e := by unfold knot whnf; rw [hs]; rfl
  rw [this]
  exact (Comp.knot_closed (σ := σ) ra mode checkFuel Comp.checkFuel_le C hok hc s hac).2.1 d e hd

end

def nctCs := ofString "nct_cs"
def nctJ := ofString "nct_j"
def nctNs := ofString "nct_ns"
def nctOuts := ofString "nct_outs"
def nctMs := ofString "nct_ms"
def nctNP := ofString "nct_np"
def nctHi := ofString "nct_hi"
def nctUs := ofString "nct_us"
def nctDH := ofString "nct_dh"
def nctDn := ofString "nct_dn"
def nctPs := ofString "nct_ps"
def nctL := ofString "nct_l"
def nctQ := ofString "nct_q"
def nctNF := ofString "nct_nf"
def nctLp := ofString "nct_lp"
def nctLn := ofString "nct_ln"
def nctNd := ofString "nct_nd"
def nctTp := ofString "nct_tp"
def nctCty := ofString "nct_cty"
def nctCr := ofString "nct_cr"
def nctTy := ofString "nct_ty"
def nctU := ofString "nct_u"
def nctFu := ofString "nct_fu"
def nctK0 := ofString "nct_k0"
def nctN0 := ofString "nct_n0"
def nctR3 := ofString "nct_r3"
def nctKs := ofString "nct_ks"
def nctNds := ofString "nct_nds"
def nctCur := ofString "nct_cur"
def nctCl := ofString "nct_cl"
def nctU4 := ofString "nct_u4"
def nctRh := ofString "nct_rh"
def nctG := ofString "nct_g"
def nctOcc := ofString "nct_occ"
def nctNm := ofString "nct_nm"
def nctNnf := ofString "nct_nnf"
def nctNs2 := ofString "nct_ns2"
def nctOp := ofString "nct_op"
def nctOuts2 := ofString "nct_outs2"
def nctR := ofString "nct_r"
def fNct := ofString "nestCtors"

def nctParams : List MlS := [nctCs, nctJ, nctNs, nctOuts, nctMs, nctNP, nctHi, nctUs, nctDH, nctDn, nctPs]
def nctLocals : List MlS := [nctL, nctQ, nctNF, nctLp, nctLn, nctNd, nctTp, nctCty, nctCr, nctTy, nctU, nctFu, nctK0,
  nctN0, nctR3, nctKs, nctNds, nctCur, nctCl, nctU4, nctRh, nctG, nctOcc, nctNm, nctNnf, nctNs2, nctOp, nctOuts2, nctR]

/-- The tail of one constructor's walk: the result head and indices, the record, the outputs, the next. -/
def nctTail (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, nctRh), none)) fNrh [vv nctCur])
  (.ite (.cmp .equal (vv nctRh) (.const 0)) hang
  (.seq (.call (some (some (.local, nctG), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv nctCur])
  (.seq (.call (some (some (.local, nctOcc), none)) fAnyNoc [vv nctG, .const 0, vv nctMs, vv nctNP, vv nctHi])
  (.ite (.cmp .equal (vv nctOcc) (.const 0))
    (.seq (.assign .local nctNm (.load .one (vv nctQ)))
    (.seq (.call (some (some (.local, nctNnf), none)) fNnf
        [vv nctNm, vv nctUs, vv nctPs, vv nctCl, vv nctMs, vv nctNP, vv nctPs])
    (.seq (.call (some (some (.local, nctNs2), none)) ExPre.fAppend [vv nctNs, vv nctNnf])
    (alloc2 C nctOp (vv nctKs) (vv nctCl)
    (.seq (.call (some (some (.local, nctOuts2), none)) ExPre.fAppend [vv nctOuts, vv nctOp])
    (.seq (.call (some (some (.local, nctR), none)) fNct
        [vv nctCs, .op .add [vv nctJ, .const 1], vv nctNs2, vv nctOuts2, vv nctMs, vv nctNP, vv nctHi, vv nctUs, vv nctDH,
          vv nctDn, vv nctPs])
      (.return (vv nctR))))))))
    hang))))

/-- One constructor's walk up to U4. -/
def nctStep (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local nctQ (.load .one (.op .add [.op .add [vv nctCs, .const 8], .shift .lsl (vv nctJ) (.const 4)])))
  (.seq (.assign .local nctNF (.load .one (.op .add [.op .add [vv nctCs, .const 16], .shift .lsl (vv nctJ) (.const 4)])))
  (.seq (.assign .local nctLp (.load .one (.op .add [vv nctQ, .const 8])))
  (.seq (.assign .local nctLn (.load .one (vv nctLp)))
  (.seq (.call (some (some (.local, nctNd), none)) fNdg [vv nctLp, .const 0, vv nctLn])
  (.ite (.cmp .equal (vv nctNd) (.const 0)) hang
  (.seq (.assign .local nctTp (.load .one (.op .add [vv nctQ, .const 16])))
  (.seq (.call (some (some (.local, nctCty), none)) ILP.fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv nctTp, vv nctLp, vv nctUs])
  (.seq (.call (some (some (.local, nctCr), none)) fNcr [vv nctMs, vv nctUs, vv nctDn, vv nctDH, vv nctCty])
  (.seq (.call (some (some (.local, nctTy), none)) fI [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctCr])
  (.seq (.call (some (some (.local, nctU), none)) fEns [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctTy])
  (.seq (.call (some (some (.local, nctFu), none)) fWwf [vv nctCr])
  (.ite (.cmp .notLower (vv nctFu) (.const (BitVec.ofNat 64 (2 ^ 58)))) hang
  (alloc1 C nctK0 (.const 0) (alloc1 C nctN0 (.const 0)
  (.seq (.call (some (some (.local, nctR3), none)) fNestFields
      [vv nctFu, vv nctHi, vv nctNF, .const 0, vv nctCr, vv nctK0, vv nctN0, vv nctMs, vv nctNP, vv nctHi])
  (.seq (.assign .local nctKs (.load .one (vv nctR3)))
  (.seq (.assign .local nctNds (.load .one (.op .add [vv nctR3, .const 8])))
  (.seq (.assign .local nctCur (.load .one (.op .add [vv nctR3, .const 16])))
  (.seq (.call (some (some (.local, nctCl), none)) fCtg [vv nctHi, .const 0, vv nctNds, .const 0, vv nctCur])
  (.seq (.call (some (some (.local, nctU4), none)) fU4 [vv nctKs, .const 0, vv nctNF, vv nctCl])
  (.ite (.cmp .equal (vv nctU4) (.const 0)) (nctTail C) hang)))))))))))))))))))))

def nctBody (C : Ctx) : ProgHOL 64 := prologue nctLocals
  (.seq (.assign .local nctL (.load .one (vv nctCs)))
  (.ite (.cmp .lower (vv nctJ) (vv nctL)) (nctStep C)
    (alloc2 C nctR (vv nctOuts) (vv nctNs) (.return (vv nctR)))))

structure NCTCodes (C : Ctx) : Prop where
  nf : NFCodes C
  nt : NTCodes C
  crest : CrestCodes C
  nnf : NNFCodes C
  cc : CCCodes C
  ctg : CTGCodes C
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  ilp : ILP.CodesILP C (ILP.ilpBody C)
  ilpf : C.code.lookup ILP.fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ILP.ilpfBody C, .one)
  ens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  self : C.code.lookup fNct = some (nctParams.map (fun p => (p, ShapeHOL.one)), nctBody C, .one)

/-- A list as a block of pointers to its elements' records. -/
def PRep {α : Type} (C : Ctx) (H : List (BitVec 64)) (o : Nat) (Rep : List (BitVec 64) → Nat → α → Prop)
    (xs : List α) : Prop :=
  ∃ os : List Nat, os.length = xs.length ∧ BlkAt H o (os.map (cellA C)) ∧
    ∀ i (hi : i < xs.length) (ho : i < os.length), Rep H os[i] xs[i]

theorem pRep_mono {α : Type} {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat}
    {Rep : List (BitVec 64) → Nat → α → Prop} (hR : ∀ oi a, Rep H oi a → Rep H' oi a) {xs : List α}
    (h : PRep C H o Rep xs) : PRep C H' o Rep xs :=
  let ⟨os, h1, h2, h3⟩ := h; ⟨os, h1, blkAt_mono h2 hp, fun i hi ho => hR _ _ (h3 i hi ho)⟩

theorem pRep_snoc {α : Type} {C : Ctx} {H : List (BitVec 64)} {o' onew : Nat}
    {Rep : List (BitVec 64) → Nat → α → Prop} {xs : List α} {x : α} (os : List Nat) (h1 : os.length = xs.length)
    (h3 : ∀ i (hi : i < xs.length) (ho : i < os.length), Rep H os[i] xs[i]) (hx : Rep H onew x)
    (hb : BlkAt H o' (os.map (cellA C) ++ [cellA C onew])) : PRep C H o' Rep (xs ++ [x]) := by
  refine ⟨os ++ [onew], by simp [h1], by simpa using hb, fun i hi ho => ?_⟩
  by_cases hil : i < xs.length
  · rw [List.getElem_append_left (by omega), List.getElem_append_left hil]; exact h3 i hil (by omega)
  · have hi' : i = xs.length := by simp at hi; omega
    subst hi'
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp [h1]; exact hx

/-- An output `(kinds, closed)` at `o`. -/
def OutRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (p : List NestFieldKind × EIdx) : Prop :=
  (∃ ok, H[o]? = some (cellA C ok) ∧ BlkAt H ok (p.1.map kindW)) ∧ H[o + 1]? = some (Enc.idxW p.2)

theorem outRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {p : List NestFieldKind × EIdx}
    (h : OutRep C H o p) : OutRep C H' o p :=
  let ⟨⟨ok, h1, h2⟩, h3⟩ := h; ⟨⟨ok, get_prefix h1 hp, blkAt_mono h2 hp⟩, get_prefix h3 hp⟩

theorem cellA_ctor_ptr (C : Ctx) (o j : Nat) (hj : j < 2 ^ 59) :
    cellA C o + 8 + BitVec.ofNat 64 j <<< 4 = cellA C (o + 1 + 2 * j) := by
  unfold cellA; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem cellA_ctor_nf (C : Ctx) (o j : Nat) (hj : j < 2 ^ 59) :
    cellA C o + 16 + BitVec.ofNat 64 j <<< 4 = cellA C (o + 2 + 2 * j) := by
  unfold cellA; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

section
variable {σ : Type}

theorem nct_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nctLocals → (ctxEnv C ++ nctParams.zip vals).get x = none :=
  Knot.params_none C nctLocals nctParams vals (by decide) (by decide)

/-- `nestCtors`' answer `[outs, ns]` (the state's keys and active list kept). -/
def PostNCT (C : Ctx) (ns : NestState) (r : List (List NestFieldKind × EIdx) × NestState) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o oo on, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧ PRep C H' oo (OutRep C) r.1 ∧
    H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧ r.2.keys = ns.keys ∧
    r.2.active = ns.active ∧ SR (ctxH C H') s' st

theorem postNCT_locals (C : Ctx) (ns : NestState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNCT C ns a w s' st → PostNCT C ns a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, h5, h6, hs⟩ =>
    ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, h5, h6, sr_of_eq hs rfl rfl rfl rfl⟩

end

section
variable {σ : Type}

set_option maxHeartbeats 64000000 in
/-- **`nestCtors`** at the root frame (`hi` and the group's names instantiated). -/
theorem nct_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : NCTCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (nP : Nat) (hnP : nP < 2 ^ 56) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hI : ctx.nIdxs = ms.map (·.nIdx)) (hnI : ∀ t (ht : t < ms.length), ms[t].nIdx < 2 ^ 63)
    (hpl : ctx.params.length < 2 ^ 56) (holes : List EIdx) (pdh pp : Nat)
    (hdh : BlkAt C.H pdh ((ctx.params ++ holes).map Enc.idxW)) (hpp : BlkAt C.H pp (ctx.params.map Enc.idxW))
    (vsL : List ConLeche.Level) (hlv : denoteLs C.St.lss ctx.lvls = some vsL)
    (cs : List (IConstantVal × Nat)) (ol : Nat) (hcs : CtorsRep C C.H ol cs) (hcsl : cs.length < 2 ^ 58)
    (hcv : ∀ c ∈ cs, CVDen c.1 C.St ∧ c.2 < 2 ^ 56) :
    ∀ f j (ns : NestState) (outs : List (List NestFieldKind × EIdx)) (ons oouts : Nat) (H : List (BitVec 64))
      (s : AState), cs.length - j = f → j ≤ cs.length → C.H <+: H →
      PRep C H ons (NfRep C) ns.ctorNfs.toList → PRep C H oouts (OutRep C) outs →
      SpecR (σ := σ) (Pre (ctxH C H) s (nctParams.zip [cellA C ol, BitVec.ofNat 64 j, cellA C ons, cellA C oouts,
        cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls, cellA C pdh,
        BitVec.ofNat 64 ctx.params.length, cellA C pp])) (nctBody C) s
        (nestCtors mode C.fe ctx true 0 [] (nP + ms.length) ctx.lvls ctx.params (ms.map (·.cvT.name)) holes
          (cs.drop j) ns outs) (PostNCT (ctxH C H) ns) := by
  intro f
  induction f with
  | zero =>
    intro j ns outs ons oouts H s hf hj hp hns houts
    have hjl : j = cs.length := by omega
    subst hjl
    refine specR_prologue (postNCT_locals _ _) (nct_none _ _) ?_
    have hcs' := hcs
    refine UD.specR_heapLoadI' (C := ctxH C H) nctL (vv nctCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nctParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, nestCtors]
    obtain ⟨os1, hl1, hb1, hr1⟩ := houts
    obtain ⟨os2, hl2, hb2, hr2⟩ := hns
    refine specR_alloc2I (ctxOK_H hok H) nctR (vv nctOuts) (vv nctNs) (cellA C oouts) (cellA C ons) (by decide)
      (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv])) (fun H2 ws hp2 hws => ?_)
    obtain ⟨g0, g1⟩ := img2_get H2 ws (cellA C oouts) (cellA C ons) hws
    have h2 := img2_prefix H2 ws (cellA C oouts) (cellA C ons) hws
    have hp2' : H <+: _ := (hp2 : H <+: H2).trans h2
    exact specR_returnI (vv nctR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
      ⟨_, H2.length, oouts, ons, hp2', rfl, g0,
        ⟨os1, hl1, blkAt_mono hb1 hp2', fun i hi ho => outRep_mono hp2' (hr1 i hi ho)⟩, g1,
        ⟨os2, hl2, blkAt_mono hb2 hp2', fun i hi ho => nfRep_mono hp2' (hr2 i hi ho)⟩, rfl, rfl,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j ns outs ons oouts H s hf hj hp hns houts
    have hjl : j < cs.length := by omega
    refine specR_prologue (postNCT_locals _ _) (nct_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nctL (vv nctCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nctParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, nctParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold nctStep
    obtain ⟨oc, hoc, hcvr, hnfe⟩ := hcs.2 j hjl
    have hcvj := hcv cs[j] (List.getElem_mem hjl)
    rw [List.drop_eq_getElem_cons hjl]
    generalize hcj : cs[j] = c at hoc hcvr hnfe hcvj
    obtain ⟨cv, nF⟩ := c
    rw [nestCtors]
    simp only
    refine UD.specR_heapLoadI' (C := ctxH C H) nctQ _ (ol + 1 + 2 * j) _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]; exact cellA_ctor_ptr C ol j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nctNF _ (ol + 2 + 2 * j) _ (get_prefix hnfe.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]; exact cellA_ctor_nf C ol j (by omega)) ?_
    obtain ⟨hcn, ⟨wl, hwl, olp, hwlo, hlpb⟩, hct⟩ := hcvr
    subst hwlo
    refine UD.specR_heapLoadI' (C := ctxH C H) nctLp _ (oc + 1) _ (get_prefix hwl hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nctLn (vv nctLp) olp _ (get_prefix hlpb.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    simp only at hcvj
    have hlpl : cv.levelParams.length < 2 ^ 62 := by have := hcvj.1.2.2; omega
    have hlpH : BlkAt H olp (cv.levelParams.map Enc.idxW) := blkAt_mono hlpb hp
    refine specR_callPure (C := ctxH C H) nctNd fNdg ndgParams [vv nctLp, .const 0, vv nctLn] ndgBody
      [cellA C olp, BitVec.ofNat 64 0, BitVec.ofNat 64 cv.levelParams.length] (nameNodup (cv.levelParams.drop 0))
      (by decide) rfl (by decide) hc.ndg ⟨by simp +decide [sev, Env.get_cons]; rfl, rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
        (ndg_spec C hc.ndh hc.ndg cv.levelParams olp hlpl _ 0 H s hp hlpH rfl (Nat.zero_le _)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    simp only [List.drop_zero]
    by_cases hnd : nameNodup cv.levelParams = true
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnd]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnd]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_neg (by simp [hnd])]
    refine UD.specR_heapLoadI' (C := ctxH C H1) nctTp _ (oc + 2) _ (get_prefix hct (hp.trans hp1')) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
    refine specR_callNIH (C := ctxH C H1) nctCty ILP.fInstLPF ILP.ilpParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv nctTp, vv nctLp, vv nctUs] (ILP.ilpfBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cv.type, cellA C olp, Enc.idxW ctx.lvls] (by decide) rfl (by decide) hc.ilpf
      ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (ILP.PostILP (ctxH C H1)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => by
        have hcvs := cvDen_ext hcvj.1 hu.floor
        obtain ⟨ks, hks⟩ := denoteNList_total' cv.levelParams hcvs.1
        exact Knot.specR_of_pre u (pre_of_lookups hu ILP.ilpParams _ rfl hlk)
          (ILP.ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt olp cv.levelParams ks ctx.lvls vsL H1 s cv.type
            hks (denoteLs_ext hlv hu.floor) (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls hcvs.2.1
            (blkAt_mono hlpH hp1')))
      (fun cty w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    have hpH2 : C.H <+: H2 := (hp.trans hp1').trans hp2'
    refine specR_callNIH (C := ctxH C H2) nctCr fNcr ncrParams [vv nctMs, vv nctUs, vv nctDn, vv nctDH, vv nctCty] ncrBody
      [cellA C om, Enc.idxW ctx.lvls, BitVec.ofNat 64 ctx.params.length, cellA C pdh, Enc.idxW cty] (by decide) rfl
      (by decide) hc.crest.ncr ⟨(by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp [sev, Env.get_cons], trivial⟩
      (PostSomeH (ctxH C H2)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
      (fun o w s' st ⟨H', t, hp', ho, hw, hsr⟩ => ⟨H', hp', ⟨t, ho, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ncrParams _ rfl hlk)
        (ncr_spec ra C hok hc.crest ms om (by omega) hM ctx.lvls ctx.params holes (by omega) pdh cty H2 hpH2
          (blkAt_mono hdh hpH2) s2))
      (fun o w s3 H3 hp3 ⟨cr, ho, hw⟩ => ?_)
    subst ho; subst hw
    have hp3' : H2 <+: H3 := hp3
    have hpH3 : C.H <+: H3 := hpH2.trans hp3'
    simp only
    have hkH3 := kcodes_H hk H3
    refine Big.specR_callKC (C := ctxH C H3) nctTy fI kParams [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctCr]
      (inferE (ctxH C H3) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 (nP + ms.length), Enc.idxW cr] (by decide) rfl
      (by decide) hkH3.ei ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp [sev, Env.get_cons], trivial⟩
      (Comp.inferTop ra mode (ctxOK_H hok H3) hkH3 (allCodes_H hac H3) hs s3 (nP + ms.length) (by omega) cr)
      (fun ty s4 H4 hp4 _ => ?_)
    have hp4' : H3 <+: H4 := hp4
    have hpH4 : C.H <+: H4 := hpH3.trans hp4'
    refine specR_callNIH (C := ctxH C H4) nctU fEns kParams [.const (BitVec.ofNat 64 checkFuel), vv nctHi, vv nctTy]
      ensBody [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 (nP + ms.length), Enc.idxW ty] (by decide) rfl (by decide) hc.ens
      ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp [sev, Env.get_cons], trivial⟩
      (PostLH (ctxH C H4)) (fun u w s' H' => w = Enc.idxW u) (fun u w s' st ⟨H', hp', hw, hsr, _⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk)
        (ens_topD ra mode (ctxOK_H hok H4) (kcodes_H hk H4) (allCodes_H hac H4) hs s4 (nP + ms.length) (by omega) ty))
      (fun u w s5 H5 hp5 hw => ?_)
    have hp5' : H4 <+: H5 := hp5
    have hpH5 : C.H <+: H5 := hpH4.trans hp5'
    simp only [↓reduceDIte, bind_assoc]
    refine specR_callNIH (C := ctxH C H5) nctFu fWwf wwParams [vv nctCr] wwBody [Enc.idxW cr] (by decide) rfl (by decide)
      hc.cc.ww ⟨(by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (PostNB (ctxH C H5)) (fun r w _ _ => w = BitVec.ofNat 64 r ∧ r < 2 ^ 63)
      (fun r w s' st ⟨H', hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu wwParams _ rfl hlk) (ww_spec C hok hc.cc cr H5 hpH5 s5))
      (fun fu w s6 H6 hp6 ⟨hw, hfu⟩ => ?_)
    subst hw
    have hp6' : H5 <+: H6 := hp6
    have hpH6 : C.H <+: H6 := hpH5.trans hp6'
    have hfw := ConPanqueque.T.Decl.nd_lt_iff fu (2 ^ 58) (by omega) (by omega)
    by_cases hfu58 : fu < 2 ^ 58
    swap
    · exact specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hWc : ∀ (H' : List (BitVec 64)) s1, C.H <+: H' → ∀ d e', d < 2 ^ 63 → Callee (σ := σ) (ctxH C H') kParams
        [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 (whnf mode C.fe checkFuel d e')
        (PostK (ctxH C H')) := fun H' s1 _ d e' hd =>
      whnfTop ra mode (ctxOK_H hok H') (kcodes_H hk H') (allCodes_H hac H') hs s1 d hd e'
    refine specR_alloc1I (ctxOK_H hok H6) nctK0 (.const 0) 0 (by decide) (fun _ => rfl) (fun Ha wsa hpa hwsa => ?_)
    have ga : ((Ha ++ wsa).set Ha.length 0)[Ha.length]? = some 0 := by simp [List.getElem?_set, hwsa]
    have hpa' : H6 <+: _ := (hpa : H6 <+: Ha).trans (img1_prefix Ha wsa 0 hwsa)
    refine specR_alloc1I (ctxOK_H hok _) nctN0 (.const 0) 0 (by decide) (fun _ => rfl) (fun Hb wsb hpb hwsb => ?_)
    have gb : ((Hb ++ wsb).set Hb.length 0)[Hb.length]? = some 0 := by simp [List.getElem?_set, hwsb]
    have hpb' : _ <+: _ := (hpb : _ <+: Hb).trans (img1_prefix Hb wsb 0 hwsb)
    have hpH7 : C.H <+: ((Hb ++ wsb).set Hb.length 0) := (hpH6.trans hpa').trans hpb'
    have hk0 : BlkAt ((Hb ++ wsb).set Hb.length 0) Ha.length (([] : List NestFieldKind).map kindW) :=
      ⟨by have := get_prefix ga hpb'; simpa using this, fun i hi => by simp at hi⟩
    have hn0 : BlkAt ((Hb ++ wsb).set Hb.length 0) Hb.length (([] : List EIdx).map Enc.idxW) :=
      ⟨by simpa using gb, fun i hi => by simp at hi⟩
    refine specR_callNIH (C := ctxH C _) nctR3 fNestFields nfParams
      [vv nctFu, vv nctHi, vv nctNF, .const 0, vv nctCr, vv nctK0, vv nctN0, vv nctMs, vv nctNP, vv nctHi] (nfBody C)
      [BitVec.ofNat 64 fu, BitVec.ofNat 64 (nP + ms.length), BitVec.ofNat 64 nF, BitVec.ofNat 64 0, Enc.idxW cr,
        cellA C Ha.length, cellA C Hb.length, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)]
      (by decide) rfl (by decide) hc.nf.self
      ⟨by simp +decide [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl,
        (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (PostNF (ctxH C _) ns) (fun r w _ H' => ∃ o ok on, w = cellA C o ∧ H'[o]? = some (cellA C ok) ∧
        BlkAt H' ok (r.1.map kindW) ∧ H'[o + 1]? = some (cellA C on) ∧ BlkAt H' on (r.2.1.map Enc.idxW) ∧
        H'[o + 2]? = some (Enc.idxW r.2.2.1) ∧ r.2.2.2 = ns)
      (fun r w s' st ⟨H', o, ok, on, hp', hw, h1, h2, h3, h4, h5, h6, hsr⟩ =>
        ⟨H', hp', ⟨o, ok, on, hw, h1, h2, h3, h4, h5, h6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nfParams _ rfl hlk)
        (nf_spec ra mode C hok hc.nf ms om hM (by omega) nP (by omega) ctx hN hP hI hnI ns hWc fu (nP + ms.length)
          nF 0 cr [] [] Ha.length Hb.length _ s6 hpH7 (by omega) hk0 hn0))
      (fun r w s7 H7 hp7 ⟨o7, ok, on, hw7, h70, hks, h71, hnds, h72, hns2⟩ => ?_)
    subst hw7
    obtain ⟨ks, nds, cur, ns2⟩ := r
    simp only at hks hnds h72 hns2
    subst ns2
    have hp7' : _ <+: H7 := hp7
    have hpH7' : C.H <+: H7 := hpH7.trans hp7'
    simp only
    refine UD.specR_heapLoadI' (C := ctxH C H7) nctKs (vv nctR3) o7 _ h70 (by decide) (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H7) nctNds _ (o7 + 1) _ h71 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o7) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H7) nctCur _ (o7 + 2) _ h72 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C o7 2) ?_
    refine specR_atEntry fun t7 ht7 => ?_
    have hndl := Big.blk_small0 (ctxOK_H hok H7) ht7.sr hnds
    have hksl := Big.blk_small0 (ctxOK_H hok H7) ht7.sr hks
    simp only [List.length_map] at hndl hksl
    unfold closeTelescope
    refine specR_callNIH (C := ctxH C H7) nctCl fCtg ctgParams [vv nctHi, .const 0, vv nctNds, .const 0, vv nctCur] ctgBody
      [BitVec.ofNat 64 (nP + ms.length), BitVec.ofNat 64 0, cellA C on, BitVec.ofNat 64 0, Enc.idxW cur] (by decide) rfl
      (by decide) hc.ctg.self
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp [sev, Env.get_cons], trivial⟩
      (PostK (ctxH C H7)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctgParams _ rfl hlk)
        (ctg_spec ra C hok hc.ctg (nP + ms.length) (by omega) nds on hndl cur _ 0 0 H7 s7 rfl (by omega) (by omega)
          hpH7' hnds))
      (fun cl w s8 H8 hp8 hw => ?_)
    subst hw
    have hp8' : H7 <+: H8 := hp8
    have hpH8 : C.H <+: H8 := hpH7'.trans hp8'
    have hrg : (List.range nF).anyM (fun i => if (ks[i]?.map (· == NestFieldKind.ordinary)).getD true then pure false
        else structUsedLater cl 0 i) = (List.range' 0 (nF - 0)).anyM (u4G ks cl) := by
      simp [List.range_eq_range']; rfl
    rw [hrg]
    refine specR_callNIH (C := ctxH C H8) nctU4 fU4 u4Params [vv nctKs, .const 0, vv nctNF, vv nctCl] u4Body
      [cellA C ok, BitVec.ofNat 64 0, BitVec.ofNat 64 nF, Enc.idxW cl] (by decide) rfl (by decide) hc.cc.u4
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H8)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu u4Params _ rfl hlk)
        (u4_spec C hok hc.cc ks cl nF ok (by omega) (by omega) _ 0 H8 s8 rfl (by omega) hpH8 (blkAt_mono hks hp8')))
      (fun u4 w s9 H9 hp9 hw => ?_)
    subst hw
    have hp9' : H8 <+: H9 := hp9
    have hpH9 : C.H <+: H9 := hpH8.trans hp9'
    cases u4
    swap
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold nctTail
    simp only [bind_assoc, hN, hP]
    refine specR_callNIH (C := ctxH C H9) nctRh fNrh nrhParams [vv nctCur] nrhBody [Enc.idxW cur] (by decide) rfl
      (by decide) hc.cc.nrh ⟨(by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (PostB (ctxH C H9)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nrhParams _ rfl hlk) (nrh_spec C hc.cc cur H9 s9))
      (fun rh w s10 H10 hp10 hw => ?_)
    subst hw
    have hp10' : H9 <+: H10 := hp10
    have hpH10 : C.H <+: H10 := hpH9.trans hp10'
    cases rh
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte, bind_assoc]
    refine specR_callNIH (C := ctxH C H10) nctG ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv nctCur]
      (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cur] (by decide) rfl (by decide) hc.nf.np.gaa
      ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (PostA (ctxH C H10)) (fun a w _ H' => ∃ o3, w = cellA C o3 ∧ BlkAt H' o3 (a.map Enc.idxW))
      (fun a w s' st ⟨H', o3, hp, hw, hb, hsr⟩ => ⟨H', hp, ⟨o3, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec (ctxH C H10) (ctxOK_H hok H10) hc.nf.np.gaa coreWalkFuel CV.coreWalkFuel_lt H10 cur s10))
      (fun args wg s11 H11 hp11 ⟨oa, hwg, hba⟩ => ?_)
    subst hwg
    have hp11' : H10 <+: H11 := hp11
    have hpH11 : C.H <+: H11 := hpH10.trans hp11'
    refine specR_atEntry fun t11 ht11 => ?_
    have hargl := Big.blk_small0 (ctxOK_H hok H11) ht11.sr hba
    simp only [List.length_map] at hargl
    refine specR_callNIH (C := ctxH C H11) nctOcc fAnyNoc ayParams [vv nctG, .const 0, vv nctMs, vv nctNP, vv nctHi]
      ayBody [cellA C oa, BitVec.ofNat 64 0, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)]
      (by decide) rfl (by decide) hc.nt.any
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl,
        (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), trivial⟩
      (PostB (ctxH C H11)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ayParams _ rfl hlk)
        (ay_spec C hok hc.nt ms om hM (by omega) nP (nP + ms.length) (by omega) (by omega) args oa hargl _ 0 H11 s11
          rfl (by omega) hpH11 hba))
      (fun occ w s12 H12 hp12 hw => ?_)
    subst hw
    have hp12' : H11 <+: H12 := hp12
    have hpH12 : C.H <+: H12 := hpH11.trans hp12'
    try simp only [List.drop_zero]
    cases occ
    swap
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.not_false, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hHH12 : H <+: H12 := (((((((((hp1'.trans hp2').trans hp3').trans hp4').trans hp5').trans hp6').trans
      (hpa'.trans hpb')).trans hp7').trans hp8').trans hp9').trans hp10' |>.trans hp11' |>.trans hp12'
    refine UD.specR_heapLoadI' (C := ctxH C H12) nctNm (vv nctQ) oc _ (get_prefix hcn (hp.trans hHH12)) (by decide)
      (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    refine specR_callNIH (C := ctxH C H12) nctNnf fNnf nnfParams
      [vv nctNm, vv nctUs, vv nctPs, vv nctCl, vv nctMs, vv nctNP, vv nctPs] (nnfBody C)
      [Enc.idxW cv.name, Enc.idxW ctx.lvls, cellA C pp, Enc.idxW cl, cellA C om, BitVec.ofNat 64 nP, cellA C pp]
      (by decide) rfl (by decide) hc.nnf.self
      ⟨by simp +decide [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]),
        by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl, trivial⟩
      (PostNNF (ctxH C H12)) (fun nf w _ H' => ∃ o, w = cellA C o ∧ NfRep C H' o nf)
      (fun nf w s' st ⟨H', o, hp', hw, h1, hsr⟩ => ⟨H', hp', ⟨o, hw, h1⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nnfParams _ rfl hlk)
        (nnf_spec ra C hok hc.nnf ctx ms om nP pp (by omega) hM hN hP (by omega) (by omega) cv cl H12 hpH12
          (blkAt_mono hpp hpH12) s12))
      (fun nf w s13 H13 hp13 ⟨onf, hwn, hnf⟩ => ?_)
    subst hwn
    have hp13' : H12 <+: H13 := hp13
    obtain ⟨os2, hl2, hb2, hr2⟩ := pRep_mono (hHH12.trans hp13') (fun _ _ => nfRep_mono (hHH12.trans hp13')) hns
    refine specR_appendI hok hc.nnf.app H13 nctNs2 (vv nctNs) (vv nctNnf) (os2.map (cellA C)) (cellA C onf) ons hb2
      (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]) (by simp +decide [sev, Env.get_cons]) (fun H14 ons2 hp14 hb14 => ?_)
    have hnsP : PRep C H14 ons2 (NfRep C) (ns.ctorNfs.toList ++ [nf]) :=
      pRep_snoc os2 hl2 (fun i hi ho => nfRep_mono hp14 (hr2 i hi ho)) (nfRep_mono hp14 hnf) hb14
    have hks14 : BlkAt H14 ok (ks.map kindW) := blkAt_mono hks ((((hp8'.trans hp9').trans hp10').trans hp11').trans
      hp12' |>.trans hp13' |>.trans hp14)
    refine specR_alloc2I (ctxOK_H hok H14) nctOp (vv nctKs) (vv nctCl) (cellA C ok) (Enc.idxW cl) (by decide)
      (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv])) (fun H15 ws15 hp15 hws15 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H15 ws15 (cellA C ok) (Enc.idxW cl) hws15
    have h15 := img2_prefix H15 ws15 (cellA C ok) (Enc.idxW cl) hws15
    have hp15' : H14 <+: _ := (hp15 : H14 <+: H15).trans h15
    obtain ⟨os1, hl1, hb1, hr1⟩ := pRep_mono ((((hHH12.trans hp13').trans hp14).trans hp15'))
      (fun _ _ => outRep_mono ((((hHH12.trans hp13').trans hp14).trans hp15'))) houts
    refine specR_appendI hok hc.nnf.app _ nctOuts2 (vv nctOuts) (vv nctOp) (os1.map (cellA C)) (cellA C H15.length)
      oouts hb1 (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]) (by simp +decide [sev, Env.get_cons] <;> rfl) (fun H16 oo2 hp16 hb16 => ?_)
    have hout2 : PRep C H16 oo2 (OutRep C) (outs ++ [(ks, cl)]) :=
      pRep_snoc os1 hl1 (fun i hi ho => outRep_mono hp16 (hr1 i hi ho))
        (outRep_mono hp16 ⟨⟨ok, k0, blkAt_mono hks14 hp15'⟩, k1⟩) hb16
    have hpH16 : C.H <+: H16 := ((((hp.trans hHH12).trans hp13').trans hp14).trans hp15').trans hp16
    refine specR_congr (m' := nestCtors mode C.fe ctx true 0 [] (nP + ms.length) ctx.lvls ctx.params
      (ms.map (·.cvT.name)) holes (cs.drop (j + 1)) { ns with ctorNfs := ns.ctorNfs.push nf } (outs ++ [(ks, cl)]) >>=
      fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H16) nctR fNct nctParams
      [vv nctCs, .op .add [vv nctJ, .const 1], vv nctNs2, vv nctOuts2, vv nctMs, vv nctNP, vv nctHi, vv nctUs, vv nctDH,
        vv nctDn, vv nctPs] (nctBody C)
      [cellA C ol, BitVec.ofNat 64 (j + 1), cellA C ons2, cellA C oo2, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls, cellA C pdh, BitVec.ofNat 64 ctx.params.length, cellA C pp]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]),
        by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv]),
        by simp +decide [sev, Env.get_cons, Env.get, nctParams, ctxEnv] <;> rfl, trivial⟩
      (PostNCT (ctxH C H16) { ns with ctorNfs := ns.ctorNfs.push nf }) (fun r w _ H' => ∃ o oo on, w = cellA C o ∧
        H'[o]? = some (cellA C oo) ∧ PRep C H' oo (OutRep C) r.1 ∧ H'[o + 1]? = some (cellA C on) ∧
        PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧ r.2.keys = ns.keys ∧ r.2.active = ns.active)
      (fun r w s' st ⟨H', o, oo, on, hp', hw, h1, h2, h3, h4, h5, h6, hsr⟩ =>
        ⟨H', hp', ⟨o, oo, on, hw, h1, h2, h3, h4, h5, h6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nctParams _ rfl hlk)
        (ih (j + 1) { ns with ctorNfs := ns.ctorNfs.push nf } (outs ++ [(ks, cl)]) ons2 oo2 H16 s13 (by omega) (by omega)
          hpH16 (by simpa using pRep_mono (hp15'.trans hp16) (fun _ _ => nfRep_mono (hp15'.trans hp16)) hnsP) hout2))
      (fun r w s17 H17 hp17 ⟨o17, oo17, on17, hw17, h1, h2, h3, h4, h5, h6⟩ => ?_)
    subst hw17
    exact specR_returnI _ (cellA C o17) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H17, o17, oo17, on17, ((hHH12.trans hp13').trans hp14).trans hp15' |>.trans hp16 |>.trans hp17,
        rfl, h1, h2, h3, h4, h5, h6, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
