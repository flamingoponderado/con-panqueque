import ConPanqueque.T.Big.WDiv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Nat.div` and `Nat.mod`

`dm(a, b)`: `b = 0` answers `0` (div) or `a` (mod), as `Nat` does. Otherwise both operands of at most one
limb divide exactly by `wdivLoop`; `a` of one limb and `b` of more answer `0` or `a`; anything larger declines
(hangs) — a resource limit of the port.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

@[simp] theorem dX_ne_rX : dX ≠ rX := by decide
@[simp] theorem rX_ne_dX : rX ≠ dX := by decide
@[simp] theorem dX_ne_rY : dX ≠ rY := by decide
@[simp] theorem rY_ne_dX : rY ≠ dX := by decide
@[simp] theorem dX_ne_rLa : dX ≠ rLa := by decide
@[simp] theorem rLa_ne_dX : rLa ≠ dX := by decide
@[simp] theorem dX_ne_rLb : dX ≠ rLb := by decide
@[simp] theorem rLb_ne_dX : rLb ≠ dX := by decide
@[simp] theorem dX_ne_rZ : dX ≠ rZ := by decide
@[simp] theorem rZ_ne_dX : rZ ≠ dX := by decide
@[simp] theorem dY_ne_rX : dY ≠ rX := by decide
@[simp] theorem rX_ne_dY : rX ≠ dY := by decide
@[simp] theorem dY_ne_rY : dY ≠ rY := by decide
@[simp] theorem rY_ne_dY : rY ≠ dY := by decide
@[simp] theorem dY_ne_rLa : dY ≠ rLa := by decide
@[simp] theorem rLa_ne_dY : rLa ≠ dY := by decide
@[simp] theorem dY_ne_rLb : dY ≠ rLb := by decide
@[simp] theorem rLb_ne_dY : rLb ≠ dY := by decide
@[simp] theorem dY_ne_rZ : dY ≠ rZ := by decide
@[simp] theorem rZ_ne_dY : rZ ≠ dY := by decide
@[simp] theorem dR_ne_rX : dR ≠ rX := by decide
@[simp] theorem rX_ne_dR : rX ≠ dR := by decide
@[simp] theorem dR_ne_rY : dR ≠ rY := by decide
@[simp] theorem rY_ne_dR : rY ≠ dR := by decide
@[simp] theorem dR_ne_rLa : dR ≠ rLa := by decide
@[simp] theorem rLa_ne_dR : rLa ≠ dR := by decide
@[simp] theorem dR_ne_rLb : dR ≠ rLb := by decide
@[simp] theorem rLb_ne_dR : rLb ≠ dR := by decide
@[simp] theorem dR_ne_rZ : dR ≠ rZ := by decide
@[simp] theorem rZ_ne_dR : rZ ≠ dR := by decide
@[simp] theorem dQ_ne_rX : dQ ≠ rX := by decide
@[simp] theorem rX_ne_dQ : rX ≠ dQ := by decide
@[simp] theorem dQ_ne_rY : dQ ≠ rY := by decide
@[simp] theorem rY_ne_dQ : rY ≠ dQ := by decide
@[simp] theorem dQ_ne_rLa : dQ ≠ rLa := by decide
@[simp] theorem rLa_ne_dQ : rLa ≠ dQ := by decide
@[simp] theorem dQ_ne_rLb : dQ ≠ rLb := by decide
@[simp] theorem rLb_ne_dQ : rLb ≠ dQ := by decide
@[simp] theorem dQ_ne_rZ : dQ ≠ rZ := by decide
@[simp] theorem rZ_ne_dQ : rZ ≠ dQ := by decide
@[simp] theorem dI_ne_rX : dI ≠ rX := by decide
@[simp] theorem rX_ne_dI : rX ≠ dI := by decide
@[simp] theorem dI_ne_rY : dI ≠ rY := by decide
@[simp] theorem rY_ne_dI : rY ≠ dI := by decide
@[simp] theorem dI_ne_rLa : dI ≠ rLa := by decide
@[simp] theorem rLa_ne_dI : rLa ≠ dI := by decide
@[simp] theorem dI_ne_rLb : dI ≠ rLb := by decide
@[simp] theorem rLb_ne_dI : rLb ≠ dI := by decide
@[simp] theorem dI_ne_rZ : dI ≠ rZ := by decide
@[simp] theorem rZ_ne_dI : rZ ≠ dI := by decide
@[simp] theorem dC_ne_rX : dC ≠ rX := by decide
@[simp] theorem rX_ne_dC : rX ≠ dC := by decide
@[simp] theorem dC_ne_rY : dC ≠ rY := by decide
@[simp] theorem rY_ne_dC : rY ≠ dC := by decide
@[simp] theorem dC_ne_rLa : dC ≠ rLa := by decide
@[simp] theorem rLa_ne_dC : rLa ≠ dC := by decide
@[simp] theorem dC_ne_rLb : dC ≠ rLb := by decide
@[simp] theorem rLb_ne_dC : rLb ≠ dC := by decide
@[simp] theorem dC_ne_rZ : dC ≠ rZ := by decide
@[simp] theorem rZ_ne_dC : rZ ≠ dC := by decide
@[simp] theorem dT_ne_rX : dT ≠ rX := by decide
@[simp] theorem rX_ne_dT : rX ≠ dT := by decide
@[simp] theorem dT_ne_rY : dT ≠ rY := by decide
@[simp] theorem rY_ne_dT : rY ≠ dT := by decide
@[simp] theorem dT_ne_rLa : dT ≠ rLa := by decide
@[simp] theorem rLa_ne_dT : rLa ≠ dT := by decide
@[simp] theorem dT_ne_rLb : dT ≠ rLb := by decide
@[simp] theorem rLb_ne_dT : rLb ≠ dT := by decide
@[simp] theorem dT_ne_rZ : dT ≠ rZ := by decide
@[simp] theorem rZ_ne_dT : rZ ≠ dT := by decide
@[simp] theorem dG_ne_rX : dG ≠ rX := by decide
@[simp] theorem rX_ne_dG : rX ≠ dG := by decide
@[simp] theorem dG_ne_rY : dG ≠ rY := by decide
@[simp] theorem rY_ne_dG : rY ≠ dG := by decide
@[simp] theorem dG_ne_rLa : dG ≠ rLa := by decide
@[simp] theorem rLa_ne_dG : rLa ≠ dG := by decide
@[simp] theorem dG_ne_rLb : dG ≠ rLb := by decide
@[simp] theorem rLb_ne_dG : rLb ≠ dG := by decide
@[simp] theorem dG_ne_rZ : dG ≠ rZ := by decide
@[simp] theorem rZ_ne_dG : rZ ≠ dG := by decide
@[simp] theorem dS_ne_rX : dS ≠ rX := by decide
@[simp] theorem rX_ne_dS : rX ≠ dS := by decide
@[simp] theorem dS_ne_rY : dS ≠ rY := by decide
@[simp] theorem rY_ne_dS : rY ≠ dS := by decide
@[simp] theorem dS_ne_rLa : dS ≠ rLa := by decide
@[simp] theorem rLa_ne_dS : rLa ≠ dS := by decide
@[simp] theorem dS_ne_rLb : dS ≠ rLb := by decide
@[simp] theorem rLb_ne_dS : rLb ≠ dS := by decide
@[simp] theorem dS_ne_rZ : dS ≠ rZ := by decide
@[simp] theorem rZ_ne_dS : rZ ≠ dS := by decide

/-- A block for a word `w` (`0` or one limb). -/
def wordBlk (C : Ctx) (v : MlS) : ProgHOL 64 :=
  allocP C rZ (.const 16) (.seq (.store (vv rZ) (.cmp .notEqual (vv v) (.const 0)))
    (.seq (.store (.op .add [vv rZ, .const 8]) (vv v)) (.return (vv rZ))))

def dmSmall (C : Ctx) (isMod : Bool) : ProgHOL 64 := if isMod then .return (vv rX) else zeroBlk C

def dmCore (C : Ctx) (isMod : Bool) : ProgHOL 64 :=
  .seq (.assign .local rLa (.load .one (vv rX)))
  (.seq (.assign .local rLb (.load .one (vv rY)))
  (.ite (.cmp .equal (vv rLb) (.const 0)) (dmSmall C isMod)
  (.ite (.cmp .lower (.const 1) (vv rLa)) hang
  (.ite (.cmp .lower (.const 1) (vv rLb)) (dmSmall C isMod)
  (.seq (.assign .local dY (.load .one (.op .add [vv rY, .const 8])))
  (.seq (.assign .local dX (.load .one (.op .add [vv rX, .panop .mul [vv rLa, .const 8]])))
  (.seq (.assign .local dR (.const 0)) (.seq (.assign .local dQ (.const 0)) (.seq (.assign .local dI (.const 0))
  (.seq wdivLoop (wordBlk C (if isMod then dR else dQ))))))))))))

def dmLocals : List MlS := [rLa, rLb, dX, dY, dR, dQ, dI, dC, dT, dG, dS, rZ]
def dmParams : List MlS := [rX, rY]
def dmBody (C : Ctx) (isMod : Bool) : ProgHOL 64 := prologue dmLocals (dmCore C isMod)

def dmRes (isMod : Bool) (a b : Nat) : Nat := if isMod then a % b else a / b

section
variable {σ : Type}

theorem limbs_word (w : Nat) (hw : w < B) : limbs w = if w = 0 then [] else [BitVec.ofNat 64 w] := by
  by_cases h : w = 0
  · subst h; simp [limbs_zero]
  · rw [ite_eq_right h, limbs_pos h, Nat.div_eq_of_lt hw, limbs_zero, Nat.mod_eq_of_lt hw]

theorem wordBlk_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} {v : MlS} (w : Nat)
    (hw : w < B) (hv : Γ.get v = some (BitVec.ofNat 64 w)) (hvz : v ≠ rZ) (hz : rZ ∈ D) :
    SpecR (σ := σ) (Inv C s Γ [] D) (wordBlk C v) s (pure w : AM Nat) (PostH C s) := by
  unfold wordBlk
  refine specR_allocI rZ (.const 16) 2 (by norm_num) hz (fun v => by simp [sev]) (fun H' ws hpre hwl hcap => ?_)
  have hj : H'.length < (ctxH C (H' ++ ws)).H.length := by show _ < (H' ++ ws).length; simp; omega
  have hB : B = 2 ^ 64 := rfl
  let hdr : BitVec 64 := BitVec.ofNat 64 (limbs w).length
  refine specR_heapStoreI (ctxOK_H hok _) (vv rZ) _ _ hj hdr (by simp; rfl) ?_ ?_
  · simp [sev, hv, hvz, hdr, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, limbs_word w hw]
    by_cases h0 : w = 0
    · simp [h0]
    · have : BitVec.ofNat 64 w ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h0]; exact this
  have hj2 : H'.length + 1 < (ctxH C ((H' ++ ws).set H'.length hdr)).H.length := by
    show _ < ((H' ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (vv v) _ hj2 (BitVec.ofNat 64 w)
    (by simp [sev, hvz]; exact cellA_add8 C _) (by simp [sev, hv, hvz]) ?_
  refine specR_returnI _ (cellA C H'.length) (by simp) (fun t ht => ?_)
  have hp1 := prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpre.length_le hdr
  have hp2 := prefix_set_ge hp1 (H'.length + 1) (by have := hpre.length_le; omega) (BitVec.ofNat 64 w)
  refine ⟨_, H'.length, hp2, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  have e1 : (((H' ++ ws).set H'.length hdr).set (H'.length + 1) (BitVec.ofNat 64 w))[H'.length]? = some hdr := by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have e2 : (((H' ++ ws).set H'.length hdr).set (H'.length + 1) (BitVec.ofNat 64 w))[H'.length + 1]? =
      some (BitVec.ofNat 64 w) := by
    rw [List.getElem?_set_self (by simp; omega)]
  refine ⟨e1, fun i hi => ?_⟩
  have hl : (limbs w).length = if w = 0 then 0 else 1 := by rw [limbs_word w hw]; split <;> rfl
  by_cases h0 : w = 0
  · rw [hl, ite_eq_left h0] at hi; omega
  have hi0 : i = 0 := by rw [hl, ite_eq_right h0] at hi; omega
  subst hi0
  rw [limbs_getElem w 0 hi]
  simpa [Nat.mod_eq_of_lt hw] using e2

theorem dm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dmLocals → (ctxEnv C ++ dmParams.zip vals).get x = none :=
  Knot.params_none C dmLocals dmParams vals (by decide) (by decide)

theorem dmSmall_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (isMod : Bool)
    (a b oa : Nat) (hba : BlkAt C.H oa (limbs a)) (hab : a < b ∨ b = 0)
    (hX : Γ.get rX = some (cellA C oa)) (hz : rZ ∈ D) :
    SpecR (σ := σ) (Inv C s Γ [] D) (dmSmall C isMod) s (pure (dmRes isMod a b) : AM Nat) (PostH C s) := by
  cases isMod
  · have : dmRes false a b = 0 := by
      rcases hab with h | h
      · exact Nat.div_eq_of_lt h
      · simp [dmRes, h]
    rw [this]; exact zeroBlk_spec hok hz
  · have : dmRes true a b = a := by
      rcases hab with h | h
      · exact Nat.mod_eq_of_lt h
      · simp [dmRes, h]
    rw [this]
    refine specR_returnI _ (cellA C oa) (by simpa [sev] using hX) (fun t ht => ?_)
    exact ⟨C.H, oa, List.prefix_refl _, rfl, hba, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

theorem dm_spec (C : Ctx) (hok : CtxOK C) (s : AState) (isMod : Bool) (a b : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs a)) (hbb : BlkAt C.H ob (limbs b)) :
    SpecR (σ := σ) (Pre C s (dmParams.zip [cellA C oa, cellA C ob])) (dmBody C isMod) s
      (pure (dmRes isMod a b) : AM Nat) (PostH C s) := by
  refine specR_prologue (postH_locals C s) (dm_none C _) ?_
  unfold dmCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs a).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs b).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' rLa (vv rX) oa _ hla0 (by decide) (by simp +decide [Env.get, dmParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' rLb (vv rY) ob _ hlb0 (by decide) (by simp +decide [Env.get, dmParams, ctxEnv]) ?_
  have hX : Env.get ((rLb, BitVec.ofNat 64 (limbs b).length) :: (rLa, BitVec.ofNat 64 (limbs a).length) ::
      (ctxEnv C ++ dmParams.zip [cellA C oa, cellA C ob])) rX = some (cellA C oa) := by
    simp +decide [Env.get, dmParams, ctxEnv]
  refine specR_atEntry fun t0 ht0 => ?_
  obtain ⟨H0, hp0, ha0⟩ := ht0.sr.heap
  have hbl := blkAt_len hba
  have hbl2 := blkAt_len hbb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  have hla58 : (limbs a).length < 2 ^ 58 := by omega
  have hlb58 : (limbs b).length < 2 ^ 58 := by omega
  have haB : a < B ^ (limbs a).length := (limbs_length_lt_iff a _).mp (Nat.le_refl _)
  have hwa := word_lt_iff 1 (limbs a).length (by decide) (by unfold B; omega)
  have hwb := word_lt_iff 1 (limbs b).length (by decide) (by unfold B; omega)
  by_cases hb0 : (limbs b).length = 0
  · have hbz : b = 0 := by
      have := (limbs_length_lt_iff b 0).mp (by omega); simpa using this
    refine specR_ifI _ 1 (by simp [sev, Env.get, hb0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact dmSmall_spec hok isMod a b oa hba (Or.inr hbz) hX (by decide)
  have hb0w : BitVec.ofNat 64 (limbs b).length ≠ 0 := fun e => hb0 (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hb0w)
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases ha1 : 1 < (limbs a).length
  · refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwa.mpr ha1])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hwa).mpr ha1])
    (fun h => absurd rfl h) (fun _ => ?_)
  have haB1 : a < B := by have := (limbs_length_lt_iff a 1).mp (by omega); simpa using this
  by_cases hb1 : 1 < (limbs b).length
  · refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwb.mpr hb1])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hbB : B ≤ b := by
      have h2 : ¬ (limbs b).length ≤ 1 := by omega
      rw [limbs_length_lt_iff] at h2; simpa using h2
    exact dmSmall_spec hok isMod a b oa hba (Or.inl (by omega)) hX (by decide)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hwb).mpr hb1])
    (fun h => absurd rfl h) (fun _ => ?_)
  have hb1' : (limbs b).length = 1 := by omega
  have hbB : b < B := by have := (limbs_length_lt_iff b 1).mp (by omega); simpa using this
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, limbs_zero] at hb1'; simp at hb1'
    · exact h
  have hbw : C.H[ob + 1 + 0]? = some (BitVec.ofNat 64 b) := by
    rw [hbb.2 0 (by omega), limbs_getElem b 0 (by omega)]
    simp only [Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt hbB]
  refine UD.specR_heapLoadI' dY _ (ob + 1 + 0) _ hbw (by decide)
    (by simp +decide [sev, Env.get, dmParams, ctxEnv]; exact cellA_add8 C _) ?_
  have haw : C.H[oa + (limbs a).length]? = some (BitVec.ofNat 64 a) := by
    rcases (by omega : (limbs a).length = 0 ∨ (limbs a).length = 1) with h | h
    · have haz : a = 0 := by have := (limbs_length_lt_iff a 0).mp (by omega); simpa using this
      rw [h, Nat.add_zero, hla0, h, haz]
    · rw [h, show oa + 1 = oa + 1 + 0 by rfl, hba.2 0 (by omega), limbs_getElem a 0 (by omega)]
      simp only [Nat.pow_zero, Nat.div_one]
      rw [Nat.mod_eq_of_lt haB1]
  refine UD.specR_heapLoadI' dX _ (oa + (limbs a).length) _ haw (by decide) (by
    simp +decide [sev, Env.get, dmParams, ctxEnv]
    have m8 : BitVec.ofNat 64 (limbs a).length * 8#64 = BitVec.ofNat 64 (8 * (limbs a).length) := CV.mul8_eq _
    rw [m8]
    unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega) ?_
  refine specR_assignI dR (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI dQ (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI dI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  let Γ0 : Env := [(dX, BitVec.ofNat 64 a), (dY, BitVec.ofNat 64 b)]
  have hB : B = 2 ^ 64 := rfl
  have ht0 : topBits a 0 = 0 := topBits_0 a (by rw [← hB]; exact haB1)
  refine specR_envWeak (Γb := wdG Γ0 a b 0) (fun z v hz => ?_) ?_
  · simp only [wdG, Γ0, ht0, Nat.zero_mod, Nat.zero_div, Env.get_cons] at hz ⊢
    by_cases e1 : z = dI
    · subst e1; simpa using hz
    by_cases e2 : z = dR
    · subst e2; simpa using hz
    by_cases e3 : z = dQ
    · subst e3; simpa using hz
    by_cases e4 : z = dX
    · subst e4; simpa using hz
    by_cases e5 : z = dY
    · subst e5; simpa using hz
    simp [e1, e2, e3, e4, e5, Env.get] at hz
  refine specR_step (wdiv_loop a b haB1 hbpos hbB (by decide) (by simp [Γ0]) (by simp [Γ0])
    (by simp [Γ0, Env.get]) (by simp [Γ0, Env.get]) (by simp [Γ0, Env.get]) (by simp [Γ0, Env.get])) ?_
  cases isMod
  · show SpecR _ (wordBlk C dQ) _ (pure (a / b)) _
    exact wordBlk_spec hok (a / b) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) haB1) (by simp [wdG, topBits_64])
      (by decide) (by decide)
  · show SpecR _ (wordBlk C dR) _ (pure (a % b)) _
    exact wordBlk_spec hok (a % b) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hbpos) (Nat.le_of_lt hbB))
      (by simp [wdG, topBits_64]) (by decide) (by decide)

end

end ConPanqueque.T.Big
