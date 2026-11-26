import ConPanqueque.T.Ind.NestPos
import ConPanqueque.T.Ex.AppendFn

/-!
# `nestFields` (no frames): a constructor's fields through `nestPos`, each opened at its variable

The accumulators (kinds, walked fields) are fresh blocks, appended to on the way in.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

section
variable {σ : Type}

/-- Append a word to a block (`appendWord`), the state kept. -/
theorem specR_appendI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hc : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (x : MlS) (src e : ExpHOL 64)
    (xs : List (BitVec 64)) (v : BitVec 64) (o : Nat) (hb : BlkAt H o xs) (hx : x ∈ D)
    (gsrc : sev Γ src = some (cellA C o)) (ge : sev Γ e = some v)
    (hk : ∀ (H' : List (BitVec 64)) o', H <+: H' → BlkAt H' o' (xs ++ [v]) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o') :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, x), none)) ExPre.fAppend [src, e]) rest) s m R := by
  refine specR_pureBind (xs ++ [v]) ?_
  refine specR_callNIH (C := ctxH C H) x ExPre.fAppend ExPre.appParams [src, e] (ExPre.appBody C) [cellA C o, v]
    (by decide) rfl hx hc ⟨gsrc, ge, trivial⟩
    (fun a w s' st => (pure (xs ++ [v]) : AM (List (BitVec 64))) s = .ok (a, s') ∧ ExPre.PostBW (ctxH C H) s a w s' st)
    (fun a w s' H' => (pure (xs ++ [v]) : AM (List (BitVec 64))) s = .ok (a, s') ∧ ∃ o, w = cellA C o ∧ BlkAt H' o a)
    (fun a w s' st ⟨hrun, _, H', o, hp', _, hw, hb, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ExPre.appParams _ rfl hlk)
      (ExPre.app_spec (ctxH C H) (ctxOK_H hok H) s o xs v hb)))
    (fun a w s2 H2 hp2 ⟨hrun, o2, hw, hb2⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs2⟩ := hrun
  subst hw; subst hs2; subst hra
  exact hk H2 o2 hp2 hb2

end

def nfFu := ofString "nf_fu"
def nfBase := ofString "nf_base"
def nfN := ofString "nf_n"
def nfJ := ofString "nf_j"
def nfCur := ofString "nf_cur"
def nfKs := ofString "nf_ks"
def nfNds := ofString "nf_nds"
def nfMs := ofString "nf_ms"
def nfNP := ofString "nf_np"
def nfHi := ofString "nf_hi"
def nfDj := ofString "nf_dj"
def nfA := ofString "nf_a"
def nfB := ofString "nf_b"
def nfQ := ofString "nf_q"
def nfK := ofString "nf_k"
def nfNd := ofString "nf_nd"
def nfF := ofString "nf_f"
def nfB2 := ofString "nf_b2"
def nfKs2 := ofString "nf_ks2"
def nfNds2 := ofString "nf_nds2"
def nfR := ofString "nf_r"
def fNestFields := ofString "nestFields"

def nfParams : List MlS := [nfFu, nfBase, nfN, nfJ, nfCur, nfKs, nfNds, nfMs, nfNP, nfHi]
def nfLocals : List MlS := gaaLocals ++ [nfDj, nfA, nfB, nfQ, nfK, nfNd, nfF, nfB2, nfKs2, nfNds2, nfR]

def nfBody (C : Ctx) : ProgHOL 64 := prologue nfLocals
  (.ite (.cmp .equal (vv nfN) (.const 0)) (alloc3 C nfR (vv nfKs) (vv nfNds) (vv nfCur) (.return (vv nfR)))
  (.ite (tagIsE nfCur 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv nfCur)) (.seq eViewP
    (.seq (.assign .local nfA (.load .one (vv lRp)))
    (.seq (.assign .local nfB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local nfDj (.op .add [vv nfBase, vv nfJ]))
    (.seq (.call (some (some (.local, nfQ), none)) fNestPos
        [vv nfFu, vv nfDj, .const 0, vv nfA, vv nfMs, vv nfNP, vv nfHi])
    (.seq (.assign .local nfK (.load .one (vv nfQ)))
    (.seq (.assign .local nfNd (.load .one (.op .add [vv nfQ, .const 8])))
    (.seq (.call (some (some (.local, nfF), none)) fInternFVar [vv nfA, vv nfDj])
    (.seq (.call (some (some (.local, nfB2), none)) ExI.fInst1F
        [.const (BitVec.ofNat 64 coreWalkFuel), vv nfB, vv nfF, .const 0])
    (.seq (.call (some (some (.local, nfKs2), none)) ExPre.fAppend [vv nfKs, vv nfK])
    (.seq (.call (some (some (.local, nfNds2), none)) ExPre.fAppend [vv nfNds, vv nfNd])
    (.seq (.call (some (some (.local, nfR), none)) fNestFields
        [vv nfFu, vv nfBase, .op .sub [vv nfN, .const 1], .op .add [vv nfJ, .const 1], vv nfB2, vv nfKs2, vv nfNds2,
          vv nfMs, vv nfNP, vv nfHi])
      (.return (vv nfR))))))))))))))))
    hang))

structure NFCodes (C : Ctx) : Prop where
  np : NPCodes C
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fNestFields = some (nfParams.map (fun p => (p, ShapeHOL.one)), nfBody C, .one)

section
variable {σ : Type}

theorem nf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nfLocals → (ctxEnv C ++ nfParams.zip vals).get x = none :=
  Knot.params_none C nfLocals nfParams vals (by decide) (by decide)

/-- `nestFields`' answer `[kinds, walked fields, residual]`, the state unchanged. -/
def PostNF (C : Ctx) (ns : NestState) (r : List NestFieldKind × List EIdx × EIdx × NestState) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o ok on, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (cellA C ok) ∧ BlkAt H' ok (r.1.map kindW) ∧
    H'[o + 1]? = some (cellA C on) ∧ BlkAt H' on (r.2.1.map Enc.idxW) ∧ H'[o + 2]? = some (Enc.idxW r.2.2.1) ∧
    r.2.2.2 = ns ∧ SR (ctxH C H') s' st

theorem postNF_locals (C : Ctx) (ns : NestState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNF C ns a w s' st → PostNF C ns a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, ok, on, hp, hw, h1, h2, h3, h4, h5, h6, hs⟩ =>
    ⟨H', o, ok, on, hp, hw, h1, h2, h3, h4, h5, h6, sr_of_eq hs rfl rfl rfl rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`nestFields`** with no frames. -/
theorem nf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hc : NFCodes C) (ms : List MemberShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (hml : ms.length < 2 ^ 59) (nP : Nat) (hnP : nP < 2 ^ 62) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name))
    (hP : ctx.nP = nP) (hI : ctx.nIdxs = ms.map (·.nIdx)) (hnI : ∀ t (ht : t < ms.length), ms[t].nIdx < 2 ^ 63)
    (ns : NestState)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 (whnf mode C.fe checkFuel d e')
      (PostK (ctxH C H)))
    (fuel base : Nat) :
    ∀ nF j (cur : EIdx) (ks : List NestFieldKind) (nds : List EIdx) (oks onds : Nat) (H : List (BitVec 64))
      (s : AState), C.H <+: H → base + j + nF + fuel < 2 ^ 62 →
      BlkAt H oks (ks.map kindW) → BlkAt H onds (nds.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (nfParams.zip [BitVec.ofNat 64 fuel, BitVec.ofNat 64 base, BitVec.ofNat 64 nF,
        BitVec.ofNat 64 j, Enc.idxW cur, cellA C oks, cellA C onds, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length)])) (nfBody C) s
        (nestFields mode C.fe ctx fuel [] base nF j cur ns ks nds) (PostNF (ctxH C H) ns) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur ks nds oks onds H s hp hb hks hnds
    refine specR_prologue (postNF_locals _ _) (nf_none _ _) ?_
    rw [nestFields]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, nfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_alloc3I (ctxOK_H hok H) nfR (vv nfKs) (vv nfNds) (vv nfCur) (cellA C oks) (cellA C onds) (Enc.idxW cur)
      (by decide) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv])) (fun H2 ws hp2 hws => ?_)
    obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (cellA C oks) (cellA C onds) (Enc.idxW cur) hws
    have h3 := img3_prefix H2 ws (cellA C oks) (cellA C onds) (Enc.idxW cur) hws
    have hp3 : H <+: _ := (hp2 : H <+: H2).trans h3
    exact specR_returnI (vv nfR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
      ⟨_, H2.length, oks, onds, hp3, rfl, g0, blkAt_mono hks hp3, g1, blkAt_mono hnds hp3, g2, rfl,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ nF ih =>
    intro j cur ks nds oks onds H s hp hb hks hnds
    refine specR_prologue (postNF_locals _ _) (nf_none _ _) ?_
    rw [nestFields]
    have hne : BitVec.ofNat 64 (nF + 1) ≠ 0#64 := ofNat_ne_zero (nF + 1) (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, nfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only
    refine Knot.specR_tagIteV nfCur cur 6 (by decide) (by decide) (by simp +decide [Env.get, nfParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (cur.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_hangI
    rw [ite_eq_left (show (cur.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, nfParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv nfCur) (Enc.idxW cur) (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP (C := ctxH C H) cur (by simp) (by simp +decide [Env.get_cons, Env.get] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, nfParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨a, b, rfl⟩ : ∃ a b, v = .forallE a b := by
      cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind cur = some (a, b) := WC.viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [WC.viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' nfA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp [sev, Env.get_cons]) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
    refine specR_loadI' nfB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
    refine specR_assignI nfDj _ (BitVec.ofNat 64 (base + j)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat]) ?_
    refine specR_callNIH (C := ctxH C H) nfQ fNestPos npParams
      [vv nfFu, vv nfDj, .const 0, vv nfA, vv nfMs, vv nfNP, vv nfHi] (npBody C)
      [BitVec.ofNat 64 fuel, BitVec.ofNat 64 (base + j), BitVec.ofNat 64 0, Enc.idxW a, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl (by decide) hc.np.self
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), rfl, (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), trivial⟩
      (PostNP (ctxH C H) ns) (fun r w _ H' => ∃ op, w = cellA C op ∧ H'[op]? = some (kindW r.1) ∧
        H'[op + 1]? = some (Enc.idxW r.2.1) ∧ r.2.2 = ns)
      (fun r w s' st ⟨H', op, hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, hw, h1, h2, h3⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu npParams _ rfl hlk)
        (np_spec ra mode C hok hc.np ms om hM hml nP hnP ctx hN hP hI hnI ns hW fuel (base + j) 0 a H s hp
          (by omega) (by omega)))
      (fun r wq s1 H1 hp1 ⟨oq, hwq, hq0, hq1, hns⟩ => ?_)
    obtain ⟨k, nd, ns2⟩ := r
    simp only at hq0 hq1 hns
    subst ns2; subst hwq
    have hp1' : H <+: H1 := hp1
    simp only
    refine UD.specR_heapLoadI' (C := ctxH C H1) nfK (vv nfQ) oq _ hq0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) nfNd _ (oq + 1) _ hq1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oq) ?_
    refine ILP.specR_internFVarI ra (ctxOK_H hok H1) hc.np.fv nfF (vv nfA) (vv nfDj) a (base + j) (by omega) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (fun fv s2 => ?_)
    refine ILP.callE_spec (C := ctxH C H1) nfB2 ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv nfB, vv nfF, .const 0] (ExI.fastBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.np.i1
      ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), rfl, trivial⟩
      (ExI.fast_spec ra (ctxH C H1) (ctxOK_H hok H1) (ExIS.codes_H C H1 hc.np.i1c) s2 coreWalkFuel b fv 0
        CV.coreWalkFuel_lt (by decide)) (fun b2 s3 => ?_)
    refine specR_appendI hok hc.app H1 nfKs2 (vv nfKs) (vv nfK) (ks.map kindW) (kindW k) oks (blkAt_mono hks hp1')
      (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (fun H2 oks2 hp2 hks2 => ?_)
    refine specR_appendI hok hc.app H2 nfNds2 (vv nfNds) (vv nfNd) (nds.map Enc.idxW) (Enc.idxW nd) onds
      (blkAt_mono hnds (hp1'.trans hp2)) (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]) (fun H3 onds2 hp3 hnds2 => ?_)
    refine specR_congr (m' := nestFields mode C.fe ctx fuel [] base nF (j + 1) b2 ns (ks ++ [k]) (nds ++ [nd]) >>=
      fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) nfR fNestFields nfParams
      [vv nfFu, vv nfBase, .op .sub [vv nfN, .const 1], .op .add [vv nfJ, .const 1], vv nfB2, vv nfKs2, vv nfNds2,
        vv nfMs, vv nfNP, vv nfHi] (nfBody C)
      [BitVec.ofNat 64 fuel, BitVec.ofNat 64 base, BitVec.ofNat 64 nF, BitVec.ofNat 64 (j + 1), Enc.idxW b2,
        cellA C oks2, cellA C onds2, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl
      (by decide) hc.self
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]; exact ofNat_succ_sub_one nF,
        by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]; exact e_succ j, (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]),
        (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nfParams, ctxEnv]), trivial⟩
      (PostNF (ctxH C H3) ns) (fun r w _ H' => ∃ o ok on, w = cellA C o ∧ H'[o]? = some (cellA C ok) ∧
        BlkAt H' ok (r.1.map kindW) ∧ H'[o + 1]? = some (cellA C on) ∧ BlkAt H' on (r.2.1.map Enc.idxW) ∧
        H'[o + 2]? = some (Enc.idxW r.2.2.1) ∧ r.2.2.2 = ns)
      (fun r w s' st ⟨H', o, ok, on, hp', hw, h1, h2, h3, h4, h5, h6, hsr⟩ =>
        ⟨H', hp', ⟨o, ok, on, hw, h1, h2, h3, h4, h5, h6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nfParams _ rfl hlk)
        (ih (j + 1) b2 (ks ++ [k]) (nds ++ [nd]) oks2 onds2 H3 s3 (((hp.trans hp1').trans hp2).trans hp3) (by omega)
          (by simpa using blkAt_mono hks2 hp3) (by simpa using hnds2)))
      (fun r w s4 H4 hp4 ⟨o, ok, on, hw, h1, h2, h3, h4, h5, h6⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C o) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H4, o, ok, on, ((hp1'.trans hp2).trans hp3).trans hp4, rfl, h1, h2, h3, h4, h5, h6,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
