import ConPanqueque.T.Ind.NestRoot

/-!
# `nestUniform` (official's `check_uniform_ind_occs`): every constructor's parameter domains name no member, and
its canonical crest has no member constant left — a constructor failing it hangs (the twin fails there)
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def pdoN := ofString "pdo_n"
def pdoE := ofString "pdo_e"
def pdoMs := ofString "pdo_ms"
def pdoLo := ofString "pdo_lo"
def pdoHi := ofString "pdo_hi"
def pdoD := ofString "pdo_d"
def pdoB := ofString "pdo_b"
def pdoO := ofString "pdo_o"
def pdoR := ofString "pdo_r"
def fPdo := ofString "piDomsOcc"

def pdoParams : List MlS := [pdoN, pdoE, pdoMs, pdoLo, pdoHi]
def pdoLocals : List MlS := gaaLocals ++ [pdoD, pdoB, pdoO, pdoR]

def pdoBody : ProgHOL 64 := prologue pdoLocals
  (.ite (.cmp .equal (vv pdoN) (.const 0)) (.return (.const 0))
  (.ite (tagIsE pdoE 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pdoE)) (.seq eViewP
    (.seq (.assign .local pdoD (.load .one (vv lRp)))
    (.seq (.assign .local pdoB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, pdoO), none)) fNocTop [vv pdoD, vv pdoMs, vv pdoLo, vv pdoHi])
    (.ite (.cmp .equal (vv pdoO) (.const 0))
      (.seq (.call (some (some (.local, pdoR), none)) fPdo
          [.op .sub [vv pdoN, .const 1], vv pdoB, vv pdoMs, vv pdoLo, vv pdoHi]) (.return (vv pdoR)))
      (.return (.const 1)))))))))
    (.return (.const 0))))

structure PDOCodes (C : Ctx) : Prop where
  nt : NTCodes C
  self : C.code.lookup fPdo = some (pdoParams.map (fun p => (p, ShapeHOL.one)), pdoBody, .one)

section
variable {σ : Type}

theorem pdo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pdoLocals → (ctxEnv C ++ pdoParams.zip vals).get x = none :=
  Knot.params_none C pdoLocals pdoParams vals (by decide) (by decide)

/-- **`piDomsOcc`** at the members' names. -/
theorem pdo_spec (C : Ctx) (hok : CtxOK C) (hc : PDOCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59) (lo hi : Nat) (hlo : lo < 2 ^ 64)
    (hhi : hi < 2 ^ 64) :
    ∀ n (e : EIdx) (H : List (BitVec 64)) (s : AState), n < 2 ^ 64 → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (pdoParams.zip [BitVec.ofNat 64 n, Enc.idxW e, cellA C om, BitVec.ofNat 64 lo,
        BitVec.ofNat 64 hi])) pdoBody s (piDomsOcc (ms.map (·.cvT.name)) lo hi n e) (PostB (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro e H s _ hp
    refine specR_prologue (postB_locals _) (pdo_none _ _) ?_
    rw [piDomsOcc]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pdoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro e H s hn hp
    refine specR_prologue (postB_locals _) (pdo_none _ _) ?_
    rw [piDomsOcc]
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) hn
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pdoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV pdoE e 6 (by decide) (by decide) (by simp +decide [Env.get, pdoParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (e.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [ite_eq_left (show (e.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, pdoParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pdoE) (Enc.idxW e) (by decide) (by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP (C := ctxH C H) e (by simp) (by simp +decide [Env.get_cons, Env.get] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, pdoParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨d, b, rfl⟩ : ∃ d b, v = .forallE d b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind e = some (d, b) := WC.viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [WC.viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' pdoD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW d) (by decide) (by simp [sev, Env.get_cons]) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW d) [Enc.idxW b] []) ?_
    refine specR_loadI' pdoB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW d) (Enc.idxW b) [] []) ?_
    refine specR_callNIH (C := ctxH C H) pdoO fNocTop ntParams [vv pdoD, vv pdoMs, vv pdoLo, vv pdoHi] ntBody
      [Enc.idxW d, cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl (by decide) hc.nt.top
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
        (nt_spec C hok hc.nt ms om hM hml lo hi hlo hhi d H s hp))
      (fun o w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases o
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := piDomsOcc (ms.map (·.cvT.name)) lo hi n b >>= fun r => pure r) (by simp only [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H1) pdoR fPdo pdoParams
        [.op .sub [vv pdoN, .const 1], vv pdoB, vv pdoMs, vv pdoLo, vv pdoHi] pdoBody
        [BitVec.ofNat 64 n, Enc.idxW b, cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl (by decide)
        hc.self
        ⟨by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv]; exact ofNat_succ_sub_one n,
          by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, pdoParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pdoParams _ rfl hlk)
          (ih b H1 s1 (by omega) (hp.trans hp1')))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW r) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp1'.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [↓reduceIte]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def nuoQ := ofString "nuo_q"
def nuoMs := ofString "nuo_ms"
def nuoNP := ofString "nuo_np"
def nuoHi := ofString "nuo_hi"
def nuoUs := ofString "nuo_us"
def nuoTp := ofString "nuo_tp"
def nuoP := ofString "nuo_p"
def nuoLp := ofString "nuo_lp"
def nuoT := ofString "nuo_t"
def nuoX := ofString "nuo_x"
def nuoO := ofString "nuo_o"
def fNuo := ofString "nestUniformOk"

def nuoParams : List MlS := [nuoQ, nuoMs, nuoNP, nuoHi, nuoUs]
def nuoLocals : List MlS := [nuoTp, nuoP, nuoLp, nuoT, nuoX, nuoO]

def nuoBody : ProgHOL 64 := prologue nuoLocals
  (.seq (.assign .local nuoTp (.load .one (.op .add [vv nuoQ, .const 16])))
  (.seq (.call (some (some (.local, nuoP), none)) fPdo [vv nuoNP, vv nuoTp, vv nuoMs, vv nuoNP, vv nuoHi])
  (.ite (.cmp .equal (vv nuoP) (.const 0))
    (.seq (.assign .local nuoLp (.load .one (.op .add [vv nuoQ, .const 8])))
    (.seq (.call (some (some (.local, nuoT), none)) ILP.fInstLPF
        [.const (BitVec.ofNat 64 coreWalkFuel), vv nuoTp, vv nuoLp, vv nuoUs])
    (.seq (.call (some (some (.local, nuoX), none)) fNcc [vv nuoMs, vv nuoUs, vv nuoNP, vv nuoT])
    (.seq (.call (some (some (.local, nuoO), none)) fNocTop [vv nuoX, vv nuoMs, .const 0, .const 0])
    (.ite (.cmp .equal (vv nuoO) (.const 0)) (.return (.const 1)) hang)))))
    hang)))

structure NUCodes (C : Ctx) : Prop where
  pdo : PDOCodes C
  crest : CrestCodes C
  ilp : ILP.CodesILP C (ILP.ilpBody C)
  ilpf : C.code.lookup ILP.fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ILP.ilpfBody C, .one)
  nuo : C.code.lookup fNuo = some (nuoParams.map (fun p => (p, ShapeHOL.one)), nuoBody, .one)

section
variable {σ : Type}

theorem nuo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nuoLocals → (ctxEnv C ++ nuoParams.zip vals).get x = none :=
  Knot.params_none C nuoLocals nuoParams vals (by decide) (by decide)

/-- `true` (else Pancake hangs), the heap extended. -/
def PostBT (C : Ctx) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ b = true ∧ w = 1 ∧ SR (ctxH C H') s' st

theorem postBT_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBT C a w s' st → PostBT C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h1, h2, hs⟩ => ⟨H', hp, h1, h2, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`nestUniformOk`** at one constructor (a `false` hangs). -/
theorem nuo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NUCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (nP : Nat) (hnP : nP < 2 ^ 56) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (vsL : List ConLeche.Level) (hlv : denoteLs C.St.lss ctx.lvls = some vsL) (cv : IConstantVal) (oc : Nat)
    (hcv : CVRep C C.H oc cv) (hcd : CVDen cv C.St) (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (nuoParams.zip [cellA C oc, cellA C om, BitVec.ofNat 64 nP,
      BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls])) nuoBody s (nestUniformOk ctx cv) (PostBT (ctxH C H)) := by
  refine specR_prologue (postBT_locals _) (nuo_none _ _) ?_
  have hhi : ctx.hiAt 0 = nP + ms.length := by simp [NestCtx.hiAt, hP, hN]
  rw [nestUniformOk, nestRootCanon]
  simp only [hhi, hN, hP]
  obtain ⟨hcn, ⟨wl, hwl, olp, hwlo, hlpb⟩, hct⟩ := hcv
  subst hwlo
  refine UD.specR_heapLoadI' (C := ctxH C H) nuoTp _ (oc + 2) _ (get_prefix hct hp) (by decide)
    (by simp +decide [sev, Env.get, nuoParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  refine specR_callNIH (C := ctxH C H) nuoP fPdo pdoParams [vv nuoNP, vv nuoTp, vv nuoMs, vv nuoNP, vv nuoHi] pdoBody
    [BitVec.ofNat 64 nP, Enc.idxW cv.type, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)]
    (by decide) rfl (by decide) hc.pdo.self ⟨(by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), trivial⟩
    (PostB (ctxH C H)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pdoParams _ rfl hlk)
      (pdo_spec C hok hc.pdo ms om hM (by omega) nP (nP + ms.length) (by omega) (by omega) nP cv.type H s (by omega) hp))
    (fun b w s1 H1 hp1 hw => ?_)
  subst hw
  have hp1' : H <+: H1 := hp1
  cases b
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine UD.specR_heapLoadI' (C := ctxH C H1) nuoLp _ (oc + 1) _ (get_prefix hwl (hp.trans hp1')) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]; exact cellA_add8 C oc) ?_
  have hlpH : BlkAt H1 olp (cv.levelParams.map Enc.idxW) := blkAt_mono hlpb (hp.trans hp1')
  refine specR_callNIH (C := ctxH C H1) nuoT ILP.fInstLPF ILP.ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv nuoTp, vv nuoLp, vv nuoUs] (ILP.ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cv.type, cellA C olp, Enc.idxW ctx.lvls] (by decide) rfl (by decide) hc.ilpf
    ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), trivial⟩
    (ILP.PostILP (ctxH C H1)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => by
      have hcvs := cvDen_ext hcd hu.floor
      obtain ⟨ks, hks⟩ := denoteNList_total' cv.levelParams hcvs.1
      exact Knot.specR_of_pre u (pre_of_lookups hu ILP.ilpParams _ rfl hlk)
        (ILP.ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt olp cv.levelParams ks ctx.lvls vsL H1 s1 cv.type
          hks (denoteLs_ext hlv hu.floor) (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls hcvs.2.1 hlpH))
    (fun t w s2 H2 hp2 hw => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  have hpH2 : C.H <+: H2 := (hp.trans hp1').trans hp2'
  refine specR_callNIH (C := ctxH C H2) nuoX fNcc nccParams [vv nuoMs, vv nuoUs, vv nuoNP, vv nuoT] (nccBody C)
    [cellA C om, Enc.idxW ctx.lvls, BitVec.ofNat 64 nP, Enc.idxW t] (by decide) rfl (by decide) hc.crest.ncc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv]), by simp [sev, Env.get_cons], trivial⟩
    (PostSomeH (ctxH C H2)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨H', t, hp', ho, hw, hsr⟩ => ⟨H', hp', ⟨t, ho, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nccParams _ rfl hlk)
      (ncc_spec ra C hok hc.crest ms om (by omega) hM ctx.lvls nP (by omega) t H2 hpH2 s2))
    (fun o w s3 H3 hp3 ⟨cr, ho, hw⟩ => ?_)
  subst ho; subst hw
  have hp3' : H2 <+: H3 := hp3
  simp only
  refine specR_callNIH (C := ctxH C H3) nuoO fNocTop ntParams [vv nuoX, vv nuoMs, .const 0, .const 0] ntBody
    [Enc.idxW cr, cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.pdo.nt.top
    ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, nuoParams, ctxEnv] <;> rfl, rfl, rfl, trivial⟩
    (PostB (ctxH C H3)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
      (nt_spec C hok hc.pdo.nt ms om hM (by omega) 0 0 (by decide) (by decide) cr H3 s3 (hpH2.trans hp3')))
    (fun occ w s4 H4 hp4 hw => ?_)
  subst hw
  cases occ
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.not_false]
    exact specR_returnI _ 1 rfl (fun tt ht => ⟨H4, ((hp1'.trans hp2').trans hp3').trans hp4, rfl, rfl,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)

end

def nulCs := ofString "nul_cs"
def nulJ := ofString "nul_j"
def nulMs := ofString "nul_ms"
def nulNP := ofString "nul_np"
def nulHi := ofString "nul_hi"
def nulUs := ofString "nul_us"
def nulL := ofString "nul_l"
def nulQ := ofString "nul_q"
def nulB := ofString "nul_b"
def nulR := ofString "nul_r"
def fNul := ofString "nestUniformCtors"

def nulParams : List MlS := [nulCs, nulJ, nulMs, nulNP, nulHi, nulUs]
def nulLocals : List MlS := [nulL, nulQ, nulB, nulR]

def nulBody : ProgHOL 64 := prologue nulLocals
  (.seq (.assign .local nulL (.load .one (vv nulCs)))
  (.ite (.cmp .lower (vv nulJ) (vv nulL))
    (.seq (.assign .local nulQ (.load .one (.op .add [.op .add [vv nulCs, .const 8], .shift .lsl (vv nulJ) (.const 4)])))
    (.seq (.call (some (some (.local, nulB), none)) fNuo [vv nulQ, vv nulMs, vv nulNP, vv nulHi, vv nulUs])
    (.seq (.call (some (some (.local, nulR), none)) fNul
        [vv nulCs, .op .add [vv nulJ, .const 1], vv nulMs, vv nulNP, vv nulHi, vv nulUs]) (.return (vv nulR)))))
    (.return (.const 1))))

def numT := ofString "num_t"
def numMs := ofString "num_ms"
def numNP := ofString "num_np"
def numHi := ofString "num_hi"
def numUs := ofString "num_us"
def numL := ofString "num_l"
def numP := ofString "num_p"
def numCs := ofString "num_cs"
def numB := ofString "num_b"
def numR := ofString "num_r"
def fNum := ofString "nestUniform"

def numParams : List MlS := [numT, numMs, numNP, numHi, numUs]
def numLocals : List MlS := [numL, numP, numCs, numB, numR]

def numBody : ProgHOL 64 := prologue numLocals
  (.seq (.assign .local numL (.load .one (vv numMs)))
  (.ite (.cmp .lower (vv numT) (vv numL))
    (.seq (.assign .local numP (.load .one (.op .add [.op .add [vv numMs, .const 8], .shift .lsl (vv numT) (.const 3)])))
    (.seq (.assign .local numCs (.load .one (.op .add [vv numP, .const 24])))
    (.seq (.call (some (some (.local, numB), none)) fNul [vv numCs, .const 0, vv numMs, vv numNP, vv numHi, vv numUs])
    (.seq (.call (some (some (.local, numR), none)) fNum
        [.op .add [vv numT, .const 1], vv numMs, vv numNP, vv numHi, vv numUs]) (.return (.const 0))))))
    (.return (.const 0))))

structure NUMCodes (C : Ctx) : Prop where
  nu : NUCodes C
  nul : C.code.lookup fNul = some (nulParams.map (fun p => (p, ShapeHOL.one)), nulBody, .one)
  num : C.code.lookup fNum = some (numParams.map (fun p => (p, ShapeHOL.one)), numBody, .one)

section
variable {σ : Type}

theorem nul_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nulLocals → (ctxEnv C ++ nulParams.zip vals).get x = none :=
  Knot.params_none C nulLocals nulParams vals (by decide) (by decide)

theorem num_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ numLocals → (ctxEnv C ++ numParams.zip vals).get x = none :=
  Knot.params_none C numLocals numParams vals (by decide) (by decide)

/-- **`cs.allM nestUniformOk`** from `j` on (a `false` hangs). -/
theorem nul_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NUMCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (nP : Nat) (hnP : nP < 2 ^ 56) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (vsL : List ConLeche.Level) (hlv : denoteLs C.St.lss ctx.lvls = some vsL) (cs : List (IConstantVal × Nat))
    (ol : Nat) (hcs : CtorsRep C C.H ol cs) (hcsl : cs.length < 2 ^ 58) (hcd : ∀ c ∈ cs, CVDen c.1 C.St) :
    ∀ f j (H : List (BitVec 64)) (s : AState), cs.length - j = f → j ≤ cs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (nulParams.zip [cellA C ol, BitVec.ofNat 64 j, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls])) nulBody s
        ((cs.drop j).allM (fun c => nestUniformOk ctx c.1)) (PostBT (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hf hj hp
    have hjl : j = cs.length := by omega
    subst hjl
    refine specR_prologue (postBT_locals _) (nul_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nulL (vv nulCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nulParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.allM]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hf hj hp
    have hjl : j < cs.length := by omega
    refine specR_prologue (postBT_locals _) (nul_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nulL (vv nulCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nulParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, nulParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcvr, -⟩ := hcs.2 j hjl
    refine UD.specR_heapLoadI' (C := ctxH C H) nulQ _ (ol + 1 + 2 * j) _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]; exact cellA_ctor_ptr C ol j (by omega)) ?_
    rw [List.drop_eq_getElem_cons hjl, List.allM]
    refine specR_callNIH (C := ctxH C H) nulB fNuo nuoParams [vv nulQ, vv nulMs, vv nulNP, vv nulHi, vv nulUs] nuoBody
      [cellA C oc, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls] (by decide) rfl
      (by decide) hc.nu.nuo ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), trivial⟩
      (PostBT (ctxH C H)) (fun b w _ _ => b = true) (fun b w s' st ⟨H', hp', hb, _, hsr⟩ => ⟨H', hp', hb, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nuoParams _ rfl hlk)
        (nuo_spec ra C hok hc.nu ms om hml hM nP hnP ctx hN hP vsL hlv cs[j].1 oc hcvr
          (hcd cs[j] (List.getElem_mem hjl)) H hp s))
      (fun b w s1 H1 hp1 hb => ?_)
    subst hb
    have hp1' : H <+: H1 := hp1
    simp only
    refine specR_congr (m' := (cs.drop (j + 1)).allM (fun c => nestUniformOk ctx c.1) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) nulR fNul nulParams
      [vv nulCs, .op .add [vv nulJ, .const 1], vv nulMs, vv nulNP, vv nulHi, vv nulUs] nulBody
      [cellA C ol, BitVec.ofNat 64 (j + 1), cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length),
        Enc.idxW ctx.lvls] (by decide) rfl (by decide) hc.nul
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nulParams, ctxEnv]), trivial⟩
      (PostBT (ctxH C H1)) (fun b w _ _ => b = true ∧ w = 1) (fun b w s' st ⟨H', hp', hb, hw, hsr⟩ => ⟨H', hp', ⟨hb, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nulParams _ rfl hlk) (ih (j + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun r w s2 H2 hp2 ⟨hr, hw⟩ => ?_)
    subst hr; subst hw
    exact specR_returnI _ 1 (by simp [sev, Env.get_cons]) (fun t ht => ⟨H2, hp1'.trans hp2, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`nestUniform`** over the members from `t` on (a failing constructor hangs). -/
theorem num_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NUMCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (nP : Nat) (hnP : nP < 2 ^ 56) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (vsL : List ConLeche.Level) (hlv : denoteLs C.St.lss ctx.lvls = some vsL)
    (hcs : ∀ m ∈ ms, m.ctors.length < 2 ^ 58 ∧ ∀ c ∈ m.ctors, CVDen c.1 C.St) :
    ∀ f t (H : List (BitVec 64)) (s : AState), ms.length - t = f → t ≤ ms.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (numParams.zip [BitVec.ofNat 64 t, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls])) numBody s
        (nestUniform ctx ((ms.drop t).map (·.ctors))) (Decl.PostU (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro t H s hf ht hp
    have htl : t = ms.length := by omega
    subst htl
    refine specR_prologue (Decl.postU_locals _) (num_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) numL (vv numMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, numParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.map_nil, nestUniform]
    exact specR_returnI _ 0 rfl (fun tt ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro t H s hf ht hp
    have htl : t < ms.length := by omega
    refine specR_prologue (Decl.postU_locals _) (num_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) numL (vv numMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, numParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff t ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, numParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr htl]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨omt, hmt, hrep⟩ := hM.2 t htl
    obtain ⟨-, -, -, ⟨ol, hol, hcsr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) numP _ (om + 1 + t) _ (get_prefix hmt hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]; show _ = cellA C (om + 1 + t)
          rw [← cellA_shl C (om + 1) t (by omega), ← cellA_add8]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) numCs _ (omt + 3) _ (get_prefix hol hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omt 3) ?_
    rw [List.drop_eq_getElem_cons htl, List.map_cons, nestUniform]
    have hmc := hcs ms[t] (List.getElem_mem htl)
    rw [show ms[t].ctors = ms[t].ctors.drop 0 from rfl]
    refine specR_callNIH (C := ctxH C H) numB fNul nulParams [vv numCs, .const 0, vv numMs, vv numNP, vv numHi, vv numUs]
      nulBody [cellA C ol, BitVec.ofNat 64 0, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length),
        Enc.idxW ctx.lvls] (by decide) rfl (by decide) hc.nul
      ⟨by simp [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), trivial⟩
      (PostBT (ctxH C H)) (fun b w _ _ => b = true) (fun b w s' st ⟨H', hp', hb, _, hsr⟩ => ⟨H', hp', hb, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nulParams _ rfl hlk)
        (nul_spec ra C hok hc ms om hml hM nP hnP ctx hN hP vsL hlv ms[t].ctors ol hcsr hmc.1 hmc.2 _ 0 H s rfl
          (by omega) hp))
      (fun b w s1 H1 hp1 hb => ?_)
    subst hb
    have hp1' : H <+: H1 := hp1
    simp only [↓reduceIte]
    refine specR_congr (m' := nestUniform ctx ((ms.drop (t + 1)).map (·.ctors)) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) numR fNum numParams
      [.op .add [vv numT, .const 1], vv numMs, vv numNP, vv numHi, vv numUs] numBody
      [BitVec.ofNat 64 (t + 1), cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls]
      (by decide) rfl (by decide) hc.num
      ⟨by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]; exact e_succ t,
        by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, numParams, ctxEnv]), trivial⟩
      (Decl.PostU (ctxH C H1)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu numParams _ rfl hlk)
        (ih (t + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun r w s2 H2 hp2 _ => ?_)
    exact specR_returnI _ 0 rfl (fun tt ht => ⟨H2, hp1'.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
