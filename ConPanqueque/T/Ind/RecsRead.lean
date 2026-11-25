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
def ulW := ofString "ul_w"
def ulT := ofString "ul_t"
def ulI := ofString "ul_i"
def ulN := ofString "ul_n"
def ulQ := ofString "ul_q"
def ulX := ofString "ul_x"
def fRulesRead := ofString "rulesRead"

def ulParams : List MlS := [ulR, ulMI, ulRP, ulW, ulT, ulI]
def ulLocals : List MlS := [ulN, ulQ, ulX]

def ulBody : ProgHOL 64 := prologue ulLocals
  (.seq (.assign .local ulN (.load .one (vv ulW)))
  (.ite (.cmp .lower (vv ulI) (vv ulN))
    (.seq (.assign .local ulQ (.load .one (.op .add [vv ulW, .shift .lsl (.op .add [vv ulI, .const 1]) (.const 3)])))
    (.seq (.call (some (some (.local, ulX), none)) fRuleReads [vv ulR, vv ulMI, vv ulRP, vv ulI, vv ulQ, vv ulT])
    (.ite (veEqC ulX 0) (.return (.const 0))
    (.seq (.call (some (some (.local, ulX), none)) fRulesRead
      [vv ulR, vv ulMI, vv ulRP, vv ulW, vv ulT, .op .add [vv ulI, .const 1]]) (.return (vv ulX))))))
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
    (crec : NIdx) (isK : Bool) (rules : List IRecRule) (hrec : C.fe.find? crec = some (.recInfo cv mI rP isK rules))
    (ow : Nat) (hrl : RulesAt C ow rules) (i : Nat) (hi : i ≤ rules.length) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hrn : rr = none → wr = 0) (hrs : ∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H ob r) (s : AState)
    (rec : i < rules.length → ∀ (H' : List (BitVec 64)) (s' : AState), C.H <+: H' →
      (∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H' ob r) →
      SpecR (Pre (σ := σ) (ctxH C H') s' (ulParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
        Enc.idxW cv.type, BitVec.ofNat 64 (i + 1)])) ulBody s'
        (rulesRead C.fe cv rr mI rP (rules.drop (i + 1)) (i + 1)) (PostB (ctxH C H'))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (ulParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
      Enc.idxW cv.type, BitVec.ofNat 64 i])) ulBody s (rulesRead C.fe cv rr mI rP (rules.drop i) i)
      (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (ul_none _ _) ?_
  let Γ0 : Env := ctxEnv (ctxH C H) ++ ulParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
      Enc.idxW cv.type, BitVec.ofNat 64 i]
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
    rw [rulesRead_drop_cons C.fe cv rr mI rP rules i hil]
    obtain ⟨q, hq, hrq⟩ := hrl.2 i hil
    refine specR_envLoadI (C := ctxH C H) ulQ _ (ow + 1 + i) (ecell C q) (by decide)
      (by
        simp only [sev, sev_vv, Env.get_cons]; simp +decide
        simp only [Γ0] at gW gI; rw [gW, gI]; simp
        show _ = ecell C (ow + 1 + i)
        simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        omega) hq ?_
    refine specR_callNIH (C := ctxH C H) ulX fRuleReads rdParams [vv ulR, vv ulMI, vv ulRP, vv ulI, vv ulQ, vv ulT]
      (rdBody C) [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, BitVec.ofNat 64 i, ecell C q, Enc.idxW cv.type]
      (by decide) rfl (by decide) hcr
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gR; exact gR,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gMI; exact gMI,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gRP; exact gRP,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gI; exact gI,
        by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gT; exact gT, trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rdParams _ rfl hlk)
        (rd_spec ra C hok hf hc hAn cv rr wr mI rP i rules[i] q hm hr (by omega) H hp hrn hrs hrq crec isK rules hrec
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
    refine specR_congr (m' := rulesRead C.fe cv rr mI rP (rules.drop (i + 1)) (i + 1) >>= fun r => pure r)
      (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) ulX fRulesRead ulParams
      [vv ulR, vv ulMI, vv ulRP, vv ulW, vv ulT, .op .add [vv ulI, .const 1]] ulBody
      [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow, Enc.idxW cv.type, BitVec.ofNat 64 (i + 1)]
      (by decide) rfl (by decide) hcl
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gR; exact gR,
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
        (rec hil H1 s1 (hp.trans hp1') (fun r hr' => by
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
    (crec : NIdx) (isK : Bool) (rules : List IRecRule) (hrec : C.fe.find? crec = some (.recInfo cv mI rP isK rules))
    (ow : Nat) (hrl : RulesAt C ow rules) (hrn : rr = none → wr = 0) :
    ∀ k i (H : List (BitVec 64)) (s : AState), rules.length - i = k → i ≤ rules.length → C.H <+: H →
      (∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H ob r) →
      SpecR (Pre (σ := σ) (ctxH C H) s (ulParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, ecell C ow,
        Enc.idxW cv.type, BitVec.ofNat 64 i])) ulBody s (rulesRead C.fe cv rr mI rP (rules.drop i) i)
        (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hp hrs
    exact ul_step ra C hok hf hc hAn hcr hcl cv rr wr mI rP hm hr crec isK rules hrec ow hrl i hi H hp hrn hrs s
      (fun h => absurd h (by omega))
  | succ k ih =>
    intro i H s hk hi hp hrs
    exact ul_step ra C hok hf hc hAn hcr hcl cv rr wr mI rP hm hr crec isK rules hrec ow hrl i hi H hp hrn hrs s
      (fun hil H' s' hp' hrs' => ih (i + 1) H' s' (by omega) (by omega) hp' hrs')

end

end ConPanqueque.T.Ind
