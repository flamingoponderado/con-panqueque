import ConPanqueque.T.Ind.RuleReads

/-!
# Every rule of a recursor reads (`rulesRead`, `recReads`, `recsRead`)

The rules are a block of rule pointers in the environment heap (`RulesE`); `rulesRead` walks it from position `i`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP

def ulR := ofString "ul_r"
def ulMI := ofString "ul_mi"
def ulRP := ofString "ul_rp"
def ulBt := ofString "ul_bt"
def ulW := ofString "ul_w"
def ulT := ofString "ul_t"
def ulI := ofString "ul_i"
def ulN := ofString "ul_n"
def ulQ := ofString "ul_q"
def ulX := ofString "ul_x"
def fRulesRead := ofString "rulesRead"

def ulParams : List MlS := [ulBt, ulR, ulMI, ulRP, ulW, ulT, ulI]
def ulLocals : List MlS := [ulN, ulQ, ulX]

def ulBody : ProgHOL 64 := prologue ulLocals
  (.seq (.assign .local ulN (.load .one (vv ulW)))
  (.ite (.cmp .lower (vv ulI) (vv ulN))
    (.seq (.assign .local ulQ (.load .one (.op .add [vv ulW, .shift .lsl (.op .add [vv ulI, .const 1]) (.const 3)])))
    (.seq (.call (some (some (.local, ulX), none)) fRuleReads [vv ulBt, vv ulR, vv ulMI, vv ulRP, vv ulI, vv ulQ, vv ulT])
    (.ite (veEqC ulX 0) (.return (.const 0))
    (.seq (.call (some (some (.local, ulX), none)) fRulesRead
      [vv ulBt, vv ulR, vv ulMI, vv ulRP, vv ulW, vv ulT, .op .add [vv ulI, .const 1]]) (.return (vv ulX))))))
    (.return (.const 1))))

def rkBt := ofString "rk_bt"
def rkE := ofString "rk_e"
def rkTg := ofString "rk_tg"
def rkT := ofString "rk_t"
def rkMI := ofString "rk_mi"
def rkRP := ofString "rk_rp"
def rkW := ofString "rk_w"
def rkR := ofString "rk_r"
def rkX := ofString "rk_x"
def fRecReads := ofString "recReads"

def rkParams : List MlS := [rkBt, rkE]
def rkLocals : List MlS := [rkTg, rkT, rkMI, rkRP, rkW, rkR, rkX]

/-- `rkE` points at a stored constant's environment record. -/
def rkBody : ProgHOL 64 := prologue rkLocals
  (.seq (.assign .local rkTg (.load .one (vv rkE)))
  (.ite (veEqC rkTg 5)
    (.seq (.assign .local rkT (.load .one (.op .add [vv rkE, .const 24])))
    (.seq (.assign .local rkMI (.load .one (.op .add [vv rkE, .const 32])))
    (.seq (.assign .local rkRP (.load .one (.op .add [vv rkE, .const 40])))
    (guardP rkMI 58 (guardP rkRP 58
    (.seq (.assign .local rkW (.load .one (.op .add [vv rkE, .const 56])))
    (.seq (.call (some (some (.local, rkR), none)) fIotaRecOf [vv rkT, vv rkMI, vv rkRP])
    (.seq (.call (some (some (.local, rkX), none)) fRulesRead [vv rkBt, vv rkR, vv rkMI, vv rkRP, vv rkW, vv rkT, .const 0])
      (.return (vv rkX))))))))))
    (.return (.const 1))))

def ksBt := ofString "ks_bt"
def ksB := ofString "ks_b"
def ksI := ofString "ks_i"
def ksN := ofString "ks_n"
def ksE := ofString "ks_e"
def ksX := ofString "ks_x"
def fRecsRead := ofString "recsRead"

def ksParams : List MlS := [ksBt, ksB, ksI]
def ksLocals : List MlS := [ksN, ksE, ksX]

/-- `ksB` points at a value-heap block of environment record pointers. -/
def ksBody : ProgHOL 64 := prologue ksLocals
  (.seq (.assign .local ksN (.load .one (vv ksB)))
  (.ite (.cmp .lower (vv ksI) (vv ksN))
    (.seq (.assign .local ksE (.load .one (.op .add [vv ksB, .shift .lsl (.op .add [vv ksI, .const 1]) (.const 3)])))
    (.seq (.call (some (some (.local, ksX), none)) fRecReads [vv ksBt, vv ksE])
    (.ite (veEqC ksX 0) (.return (.const 0))
    (.seq (.call (some (some (.local, ksX), none)) fRecsRead [vv ksBt, vv ksB, .op .add [vv ksI, .const 1]])
      (.return (vv ksX))))))
    (.return (.const 1))))

section
variable {σ : Type}

theorem ul_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ulLocals → (ctxEnv C ++ ulParams.zip vals).get x = none :=
  Knot.params_none C ulLocals ulParams vals (by decide) (by decide)

theorem rulesRead_drop_cons (fe : IFEnv) (cv : IConstantVal) (rr : Option IotaRec) (mI rP : Nat)
    (rules : List IRecRule) (i : Nat) (hi : i < rules.length) :
    rulesRead fe cv rr mI rP (rules.drop i) i = (ruleReads fe cv rr mI rP i rules[i] >>= fun r =>
      if r then rulesRead fe cv rr mI rP (rules.drop (i + 1)) (i + 1) else pure false) := by
  rw [List.drop_eq_getElem_cons hi, rulesRead]

/-- A recursor's rules as an environment block of rule pointers at `ow`. -/
def RulesAt (C : Ctx) (ow : Nat) (rules : List IRecRule) : Prop :=
  C.EH[ow]? = some (BitVec.ofNat 64 rules.length) ∧
    ∀ i (hi : i < rules.length), ∃ q, C.EH[ow + 1 + i]? = some (ecell C q) ∧ RuleE C.EB C.EH q rules[i]

theorem ul_step (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one))
    (hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one))
    (cv : IConstantVal) (rr : Option IotaRec) (wr : BitVec 64) (mI rP : Nat) (hm : mI < 2 ^ 64) (hr : rP < 2 ^ 64)
    (es : List (NIdx × Nat × IConstantInfo)) (ob0 : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (hfD : EnvDen fe C.pins C.St)
    (crec : NIdx) (isK : Bool) (rules : List IRecRule) (hrec : fe.find? crec = some (.recInfo cv mI rP isK rules))
    (ow : Nat) (hrl : RulesAt C ow rules) (i : Nat) (hi : i ≤ rules.length) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hT : BTabAt C H ob0 es)
    (hrn : rr = none → wr = 0) (hrs : ∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H ob r) (s : AState)
    (rec : i < rules.length → ∀ (H' : List (BitVec 64)) (s' : AState), C.H <+: H' → BTabAt C H' ob0 es →
      (∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H' ob r) →
      SpecR (Pre (σ := σ) (ctxH C H') s' (ulParams.zip [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
        Enc.idxW cv.type, BitVec.ofNat 64 (i + 1)])) ulBody s'
        (rulesRead fe cv rr mI rP (rules.drop (i + 1)) (i + 1)) (PostB (ctxH C H'))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (ulParams.zip [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
      Enc.idxW cv.type, BitVec.ofNat 64 i])) ulBody s (rulesRead fe cv rr mI rP (rules.drop i) i)
      (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (ul_none _ _) ?_
  let Γ0 : Env := ctxEnv (ctxH C H) ++ ulParams.zip [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
      Enc.idxW cv.type, BitVec.ofNat 64 i]
  have gBt : Γ0.get ulBt = some (cellA C ob0) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gR : Γ0.get ulR = some wr := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gMI : Γ0.get ulMI = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gRP : Γ0.get ulRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gW : Γ0.get ulW = some (ecell C ow) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gT : Γ0.get ulT = some (Enc.idxW cv.type) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  have gI : Γ0.get ulI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, ulParams, ctxEnv]
  refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
  have hEN' : C.EH.length ≤ C.EN := hEN
  have hle := hok.envLay
  have hlen : ow < C.EH.length := (List.getElem?_eq_some_iff.mp hrl.1).1
  have hrlen : ow + rules.length < C.EH.length := by
    rcases Nat.lt_or_ge 0 rules.length with h0 | h0
    · obtain ⟨q, hq, -⟩ := hrl.2 (rules.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hq).1; omega
    · omega
  refine specR_envLoadI (C := ctxH C H) ulN (vv ulW) ow (BitVec.ofNat 64 rules.length) (by decide)
    (by simp only [sev, sev_vv]; exact gW) hrl.1 ?_
  have gI' : sev ((ulN, BitVec.ofNat 64 rules.length) :: Γ0) (vv ulI) = some (BitVec.ofNat 64 i) := by
    simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI
  by_cases hil : i < rules.length
  · refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 rules.length) gI' (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hil]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [rulesRead_drop_cons fe cv rr mI rP rules i hil]
    obtain ⟨q, hq, hrq⟩ := hrl.2 i hil
    refine specR_envLoadI (C := ctxH C H) ulQ _ (ow + 1 + i) (ecell C q) (by decide)
      (by
        simp only [sev, sev_vv, Env.get_cons]; simp +decide
        simp only [Γ0] at gW gI; rw [gW, gI]; simp
        show _ = ecell C (ow + 1 + i)
        simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        omega) hq ?_
    refine specR_callNIH (C := ctxH C H) ulX fRuleReads rdParams [vv ulBt, vv ulR, vv ulMI, vv ulRP, vv ulI, vv ulQ, vv ulT]
      (rdBody C) [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, BitVec.ofNat 64 i, ecell C q, Enc.idxW cv.type]
      (by decide) rfl (by decide) hcr
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gBt; exact gBt,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gR; exact gR,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gMI; exact gMI,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gRP; exact gRP,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gI; exact gI,
        by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gT; exact gT, trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rdParams _ rfl hlk)
        (rd_spec ra C hok hf hc hAn cv rr wr mI rP i rules[i] q hm hr (by omega) H hp hrn hrs es ob0 fe hfe hfD hT
          hrq crec isK rules hrec
          (List.getElem_mem hil) s))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    rcases r
    · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ite_false]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    refine specR_congr (m' := rulesRead fe cv rr mI rP (rules.drop (i + 1)) (i + 1) >>= fun r => pure r)
      (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) ulX fRulesRead ulParams
      [vv ulBt, vv ulR, vv ulMI, vv ulRP, vv ulW, vv ulT, .op .add [vv ulI, .const 1]] ulBody
      [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow, Enc.idxW cv.type, BitVec.ofNat 64 (i + 1)]
      (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gBt; exact gBt,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gR; exact gR,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gMI; exact gMI,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gRP; exact gRP,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gW; exact gW,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gT; exact gT,
        by
          show sev _ _ = _
          rw [sev_add2 _ _ _ _ _ (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gI; exact gI) rfl]
          exact congrArg some (word_add1_eq i), trivial⟩
      (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulParams _ rfl hlk)
        (rec hil H1 s1 (hp.trans hp1') (btabAt_mono hT hp1') (fun r hr' => by
          obtain ⟨ob, hob, hrep⟩ := hrs r hr'; exact ⟨ob, hob, iotaRecRep_mono hrep hp1'⟩)))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 rules.length) gI' (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hil]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega : rules.length ≤ i)]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`rulesRead`** from position `i`. -/
theorem ul_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one))
    (hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one))
    (cv : IConstantVal) (rr : Option IotaRec) (wr : BitVec 64) (mI rP : Nat) (hm : mI < 2 ^ 64) (hr : rP < 2 ^ 64)
    (es : List (NIdx × Nat × IConstantInfo)) (ob0 : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (hfD : EnvDen fe C.pins C.St)
    (crec : NIdx) (isK : Bool) (rules : List IRecRule) (hrec : fe.find? crec = some (.recInfo cv mI rP isK rules))
    (ow : Nat) (hrl : RulesAt C ow rules) (hrn : rr = none → wr = 0) :
    ∀ k i (H : List (BitVec 64)) (s : AState), rules.length - i = k → i ≤ rules.length → C.H <+: H →
      BTabAt C H ob0 es → (∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H ob r) →
      SpecR (Pre (σ := σ) (ctxH C H) s (ulParams.zip [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
        Enc.idxW cv.type, BitVec.ofNat 64 i])) ulBody s (rulesRead fe cv rr mI rP (rules.drop i) i)
        (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp hT hrs
    exact ul_step ra C hok hf hc hAn hcr hcl cv rr wr mI rP hm hr es ob0 fe hfe hfD crec isK rules hrec ow hrl i hi H hp
      hT hrn hrs s (fun h => absurd h (by omega))
  | succ k ih =>
    intro i H s hk hi hp hT hrs
    exact ul_step ra C hok hf hc hAn hcr hcl cv rr wr mI rP hm hr es ob0 fe hfe hfD crec isK rules hrec ow hrl i hi H hp
      hT hrn hrs s (fun hil H' s' hp' hT' hrs' => ih (i + 1) H' s' (by omega) (by omega) hp' hT' hrs')

theorem rk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rkLocals → (ctxEnv C ++ rkParams.zip vals).get x = none :=
  Knot.params_none C rkLocals rkParams vals (by decide) (by decide)

/-- **`recReads`** at a stored constant. -/
theorem rk_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous) (hro : ROCodes C)
    (hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one))
    (hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one))
    (es : List (NIdx × Nat × IConstantInfo)) (ob0 : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (hfD : EnvDen fe C.pins C.St)
    (cn : NIdx) (ci : IConstantInfo) (hfind : fe.find? cn = some ci) (o : Nat) (hcie : CIE C.EB C.EH o ci)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hT : BTabAt C H ob0 es) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rkParams.zip [cellA C ob0, ecell C o])) rkBody s (recReads fe ci) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (rk_none _ _) ?_
  unfold recReads
  let Γ0 : Env := ctxEnv (ctxH C H) ++ rkParams.zip [cellA C ob0, ecell C o]
  have gBt : Γ0.get rkBt = some (cellA C ob0) := by simp +decide [Γ0, Env.get, rkParams, ctxEnv]
  have gE : Γ0.get rkE = some (ecell C o) := by simp +decide [Γ0, Env.get, rkParams, ctxEnv]
  have addr : ∀ (Γ : Env) (k : Nat), Γ.get rkE = some (ecell C o) →
      sev Γ (.op .add [vv rkE, .const (BitVec.ofNat 64 (8 * k))]) = some (ecell (ctxH C H) (o + k)) := by
    intro Γ k h; simp only [sev, sev_vv, h]; simp; exact ecell_add C o k
  cases ci with
  | recInfo cv mI rP isK rules =>
    obtain ⟨hcve, h5, ⟨hmi, hmib⟩, ⟨hrp, hrpb⟩, -, w, hw, hrules⟩ := hcie
    refine specR_envLoadI (C := ctxH C H) rkTg (vv rkE) o (BitVec.ofNat 64 5) (by decide)
      (by simp only [sev, sev_vv]; exact gE) h5 ?_
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_envLoadI (C := ctxH C H) rkT _ (o + 3) (Enc.idxW cv.type) (by decide)
      (addr _ 3 (by simp +decide [Env.get_cons]; exact gE)) (by rw [show o + 3 = o + 1 + 2 by omega]; exact hcve.2.2) ?_
    refine specR_envLoadI (C := ctxH C H) rkMI _ (o + 4) (BitVec.ofNat 64 mI) (by decide)
      (addr _ 4 (by simp +decide [Env.get_cons]; exact gE)) hmi ?_
    refine specR_envLoadI (C := ctxH C H) rkRP _ (o + 5) (BitVec.ofNat 64 rP) (by decide)
      (addr _ 5 (by simp +decide [Env.get_cons]; exact gE)) hrp ?_
    refine specR_guardI rkMI mI 58 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hm' => ?_)
    refine specR_guardI rkRP rP 58 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hr' => ?_)
    obtain ⟨ow, hwo, hl0, hcells⟩ := hrules
    refine specR_envLoadI (C := ctxH C H) rkW _ (o + 7) w (by decide)
      (addr _ 7 (by simp +decide [Env.get_cons]; exact gE)) hw ?_
    have hRA : RulesAt C ow rules := ⟨hl0, fun i hi => by
      obtain ⟨q, hq, hrq⟩ := hcells i hi; exact ⟨q, hq, hrq⟩⟩
    refine specR_callNIH (C := ctxH C H) rkR fIotaRecOf roParams [vv rkT, vv rkMI, vv rkRP] roBody
      [Enc.idxW cv.type, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP] (by decide) rfl (by decide) hro.ro
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        trivial⟩
      (PostIR (ctxH C H))
      (fun o' w' _ H' => (o' = none → w' = 0) ∧ ∀ rr, o' = some rr → ∃ ob, w' = cellA C ob ∧ IotaRecRep C H' ob rr)
      (fun o' w' s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu roParams _ rfl hlk)
        (ro_spec ra C hok hro cv mI rP hm' hr' H hp s))
      (fun rr wr s1 H1 hp1 ⟨hrn, hrs⟩ => ?_)
    have hp1' : H <+: H1 := hp1
    refine specR_congr (m' := rulesRead fe cv rr mI rP (rules.drop 0) 0 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) rkX fRulesRead ulParams [vv rkBt, vv rkR, vv rkMI, vv rkRP, vv rkW, vv rkT, .const 0]
      ulBody [cellA C ob0, wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow, Enc.idxW cv.type, BitVec.ofNat 64 0]
      (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gBt; exact gBt, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, hwo]; rfl, by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulParams _ rfl hlk)
        (ul_spec ra C hok hf hc hAn hcr hcl cv rr wr mI rP (by omega) (by omega) es ob0 fe hfe hfD cn isK rules hfind
          ow hRA hrn rules.length 0 H1 s1 (by simp) (Nat.zero_le _) (hp.trans hp1') (btabAt_mono hT hp1') hrs))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | _ =>
    obtain ⟨k, hk, hk1⟩ : ∃ k : Nat, C.EH[o]? = some (BitVec.ofNat 64 k) ∧ k ≠ 5 ∧ k < 16 := by
      first
        | exact ⟨0, hcie.2, by decide, by decide⟩
        | exact ⟨1, hcie.2.1, by decide, by decide⟩
        | exact ⟨2, hcie.2, by decide, by decide⟩
        | exact ⟨3, hcie.2.1, by decide, by decide⟩
        | exact ⟨4, hcie.2.1, by decide, by decide⟩
    refine specR_envLoadI (C := ctxH C H) rkTg (vv rkE) o (BitVec.ofNat 64 k) (by decide)
      (by simp only [sev, sev_vv]; exact gE) hk ?_
    have hne : BitVec.ofNat 64 k ≠ BitVec.ofNat 64 5 := (ofNat_eq_iff (by omega) (by decide)).not.mpr hk1.1
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ks_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ksLocals → (ctxEnv C ++ ksParams.zip vals).get x = none :=
  Knot.params_none C ksLocals ksParams vals (by decide) (by decide)

/-- A value-heap block of pointers to stored constants' environment records. -/
def RecsAt (C : Ctx) (fe : IFEnv) (H : List (BitVec 64)) (ob : Nat) (cis : List IConstantInfo) : Prop :=
  H[ob]? = some (BitVec.ofNat 64 cis.length) ∧ ∀ i (hi : i < cis.length), ∃ o n,
    H[ob + 1 + i]? = some (ecell C o) ∧ CIE C.EB C.EH o cis[i] ∧ fe.find? n = some cis[i]

theorem recsAt_mono {C : Ctx} {fe : IFEnv} {H H' : List (BitVec 64)} {ob : Nat} {cis : List IConstantInfo}
    (h : RecsAt C fe H ob cis) (hp : H <+: H') : RecsAt C fe H' ob cis :=
  ⟨ConPanqueque.T.Decl.get_prefix h.1 hp, fun i hi => by
    obtain ⟨o, n, h1, h2, h3⟩ := h.2 i hi; exact ⟨o, n, ConPanqueque.T.Decl.get_prefix h1 hp, h2, h3⟩⟩

theorem recsRead_drop_cons (fe : IFEnv) (cis : List IConstantInfo) (i : Nat) (hi : i < cis.length) :
    recsRead fe (cis.drop i) = (recReads fe cis[i] >>= fun r => if r then recsRead fe (cis.drop (i + 1))
      else pure false) := by
  rw [List.drop_eq_getElem_cons hi, recsRead]

theorem ks_step (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous) (hro : ROCodes C)
    (hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one))
    (hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one))
    (hck : C.code.lookup fRecReads = some (rkParams.map (fun p => (p, ShapeHOL.one)), rkBody, .one))
    (hcs : C.code.lookup fRecsRead = some (ksParams.map (fun p => (p, ShapeHOL.one)), ksBody, .one))
    (es : List (NIdx × Nat × IConstantInfo)) (ob0 : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (hfD : EnvDen fe C.pins C.St)
    (cis : List IConstantInfo) (ob : Nat) (i : Nat) (hi : i ≤ cis.length) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hT : BTabAt C H ob0 es) (hR : RecsAt C fe H ob cis) (s : AState)
    (rec : i < cis.length → ∀ (H' : List (BitVec 64)) (s' : AState), H <+: H' →
      SpecR (Pre (σ := σ) (ctxH C H') s' (ksParams.zip [cellA C ob0, cellA C ob, BitVec.ofNat 64 (i + 1)])) ksBody s'
        (recsRead fe (cis.drop (i + 1))) (PostB (ctxH C H'))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (ksParams.zip [cellA C ob0, cellA C ob, BitVec.ofNat 64 i])) ksBody s
      (recsRead fe (cis.drop i)) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (ks_none _ _) ?_
  let Γ0 : Env := ctxEnv (ctxH C H) ++ ksParams.zip [cellA C ob0, cellA C ob, BitVec.ofNat 64 i]
  have gBt : Γ0.get ksBt = some (cellA C ob0) := by simp +decide [Γ0, Env.get, ksParams, ctxEnv]
  have gB : Γ0.get ksB = some (cellA C ob) := by simp +decide [Γ0, Env.get, ksParams, ctxEnv]
  have gI : Γ0.get ksI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, ksParams, ctxEnv]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hblen : ob + cis.length < H.length := by
    have h0 := (List.getElem?_eq_some_iff.mp hR.1).1
    rcases Nat.lt_or_ge 0 cis.length with h | h
    · obtain ⟨o, n, h1, -, -⟩ := hR.2 (cis.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1; omega
    · omega
  have hB0 : (ctxH C H).H[ob]? = some (BitVec.ofNat 64 cis.length) := hR.1
  refine UD.specR_heapLoadI' (C := ctxH C H) ksN (vv ksB) ob _ hB0 (by decide)
    (by simp only [sev, sev_vv]; exact gB) ?_
  have gI' : sev ((ksN, BitVec.ofNat 64 cis.length) :: Γ0) (vv ksI) = some (BitVec.ofNat 64 i) := by
    simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI
  by_cases hil : i < cis.length
  · refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 cis.length) gI' (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hil]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [recsRead_drop_cons fe cis i hil]
    obtain ⟨o, n, hq, hcie, hfind⟩ := hR.2 i hil
    refine UD.specR_heapLoadI' (C := ctxH C H) ksE _ (ob + 1 + i) _ hq (by decide)
      (by
        simp only [sev, sev_vv, Env.get_cons]; simp +decide
        simp only [Γ0] at gB gI; rw [gB, gI]; simp
        show _ = cellA C (ob + 1 + i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        omega) ?_
    refine specR_callNIH (C := ctxH C H) ksX fRecReads rkParams [vv ksBt, vv ksE] rkBody [cellA C ob0, ecell C o]
      (by decide) rfl (by decide) hck
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gBt; exact gBt, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rkParams _ rfl hlk)
        (rk_spec ra C hok hf hc hAn hro hcr hcl es ob0 fe hfe hfD n cis[i] hfind o hcie H hp hT s))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    rcases r
    · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ite_false]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    refine specR_congr (m' := recsRead fe (cis.drop (i + 1)) >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) ksX fRecsRead ksParams [vv ksBt, vv ksB, .op .add [vv ksI, .const 1]] ksBody
      [cellA C ob0, cellA C ob, BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hcs
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gBt; exact gBt,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gB; exact gB,
        by
          show sev _ _ = _
          rw [sev_add2 _ _ _ _ _ (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gI; exact gI) rfl]
          exact congrArg some (word_add1_eq i), trivial⟩
      (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ksParams _ rfl hlk) (rec hil H1 s1 hp1'))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 cis.length) gI' (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hil]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega : cis.length ≤ i)]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`recsRead`** from position `i`. -/
theorem ks_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous) (hro : ROCodes C)
    (hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one))
    (hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one))
    (hck : C.code.lookup fRecReads = some (rkParams.map (fun p => (p, ShapeHOL.one)), rkBody, .one))
    (hcs : C.code.lookup fRecsRead = some (ksParams.map (fun p => (p, ShapeHOL.one)), ksBody, .one))
    (es : List (NIdx × Nat × IConstantInfo)) (ob0 : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (hfD : EnvDen fe C.pins C.St)
    (cis : List IConstantInfo) (ob : Nat) :
    ∀ k i (H : List (BitVec 64)) (s : AState), cis.length - i = k → i ≤ cis.length → C.H <+: H →
      BTabAt C H ob0 es → RecsAt C fe H ob cis →
      SpecR (Pre (σ := σ) (ctxH C H) s (ksParams.zip [cellA C ob0, cellA C ob, BitVec.ofNat 64 i])) ksBody s
        (recsRead fe (cis.drop i)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp hT hR
    exact ks_step ra C hok hf hc hAn hro hcr hcl hck hcs es ob0 fe hfe hfD cis ob i hi H hp hT hR s
      (fun h => absurd h (by omega))
  | succ k ih =>
    intro i H s hk hi hp hT hR
    exact ks_step ra C hok hf hc hAn hro hcr hcl hck hcs es ob0 fe hfe hfD cis ob i hi H hp hT hR s
      (fun hil H' s' hp' => ih (i + 1) H' s' (by omega) (by omega) (hp.trans hp') (btabAt_mono hT hp')
        (recsAt_mono hR hp'))

end

end ConPanqueque.T.Ind
