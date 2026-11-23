import ConPanqueque.T.Big.Div
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Nat.gcd`

Operands of at most one limb run Euclid's algorithm, `(x, y) := (y, x % y)` until `y = 0`, each remainder by
`wdivLoop`; larger operands decline (hang). The loop is counted by the ghost `eSteps x y`.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def euS (p : Nat × Nat) : Nat × Nat := (p.2, p.1 % p.2)

def eSteps (x y : Nat) : Nat := if h : y = 0 then 0 else eSteps y (x % y) + 1
termination_by y
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem eu_facts : ∀ y x, (∀ i, i < eSteps x y → (euS^[i] (x, y)).2 ≠ 0) ∧ (euS^[eSteps x y] (x, y)).2 = 0 ∧
    (euS^[eSteps x y] (x, y)).1 = Nat.gcd x y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro x
    by_cases h : y = 0
    · subst h
      have e : eSteps x 0 = 0 := by rw [eSteps]; simp
      rw [e]; exact ⟨fun i hi => absurd hi (by omega), rfl, by simp⟩
    have e : eSteps x y = eSteps y (x % y) + 1 := by rw [eSteps]; simp [h]
    obtain ⟨h1, h2, h3⟩ := ih (x % y) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) y
    have hit : ∀ k, euS^[k + 1] (x, y) = euS^[k] (y, x % y) := fun k => by
      rw [Function.iterate_succ_apply]; rfl
    rw [e]
    refine ⟨fun i hi => ?_, by rw [hit]; exact h2, ?_⟩
    · rcases i with _ | i
      · exact h
      · rw [hit]; exact h1 i (by omega)
    · rw [hit, h3, Nat.gcd_comm y, ← Nat.gcd_rec y x, Nat.gcd_comm]

theorem eu_lt (b : Nat) : ∀ i (p : Nat × Nat), p.1 < b → p.2 < b → (euS^[i] p).1 < b ∧ (euS^[i] p).2 < b := by
  intro i
  induction i with
  | zero => intro p h1 h2; exact ⟨h1, h2⟩
  | succ i ih =>
    intro p h1 h2
    rw [Function.iterate_succ_apply]
    exact ih _ h2 (Nat.lt_of_le_of_lt (Nat.mod_le _ _) h1)

def gcdBody1 : ProgHOL 64 :=
  .seq (.assign .local dR (.const 0)) (.seq (.assign .local dQ (.const 0)) (.seq (.assign .local dI (.const 0))
  (.seq wdivLoop (.seq (.assign .local dX (vv dY)) (.assign .local dY (vv dR))))))

def gcdCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rLa (.load .one (vv rX)))
  (.seq (.assign .local rLb (.load .one (vv rY)))
  (.ite (.cmp .lower (.const 1) (vv rLa)) hang
  (.ite (.cmp .lower (.const 1) (vv rLb)) hang
  (.seq (.assign .local dX (.load .one (.op .add [vv rX, .panop .mul [vv rLa, .const 8]])))
  (.seq (.assign .local dY (.load .one (.op .add [vv rY, .panop .mul [vv rLb, .const 8]])))
  (.seq (.while (.cmp .notEqual (vv dY) (.const 0)) gcdBody1) (wordBlk C dX)))))))

def gcdBody (C : Ctx) : ProgHOL 64 := prologue dmLocals (gcdCore C)

section
variable {σ : Type}

def gcG (Γb : Env) (p : Nat × Nat) (i : Nat) : Env :=
  (dX, BitVec.ofNat 64 (euS^[i] p).1) :: (dY, BitVec.ofNat 64 (euS^[i] p).2) :: Γb

theorem gcd_loop {α : Type} {C : Ctx} {s : AState} {D : List MlS} {Γb : Env} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (hx : x < B) (hy : y < B)
    (hD : dS ∈ D ∧ dC ∈ D ∧ dT ∈ D ∧ dR ∈ D ∧ dG ∈ D ∧ dQ ∈ D ∧ dI ∈ D ∧ dX ∈ D ∧ dY ∈ D)
    (hnS : Γb.get dS = none) (hnC : Γb.get dC = none) (hnT : Γb.get dT = none) (hnG : Γb.get dG = none)
    (hnI : Γb.get dI = none) (hnR : Γb.get dR = none) (hnQ : Γb.get dQ = none)
    (hr : SpecR (Inv C s (gcG Γb (x, y) (eSteps x y)) [] D) rest s m R) :
    SpecR (Inv C s (gcG Γb (x, y) 0) [] D) (.seq (.while (.cmp .notEqual (vv dY) (.const 0)) gcdBody1) rest) s m R := by
  obtain ⟨ds, dc, dt, dr, dg', dq, di, dx, dy⟩ := hD
  obtain ⟨hne, -, -⟩ := eu_facts y x
  have hz := (eu_facts y x).2.1
  have hlt := fun i => eu_lt B i (x, y) hx hy
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (eSteps x y) (fun _ => C) (gcG Γb (x, y))
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 (euS^[i] (x, y)).2) 0
      then 1 else 0, by simp [sev, gcG, Env.get], ?_⟩) (fun i hi => ?_) hr
  · have hb := (hlt i).2
    have e : BitVec.ofNat 64 (euS^[i] (x, y)).2 = 0 ↔ (euS^[i] (x, y)).2 = 0 := by
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; unfold B at hb; omega
      · intro h; rw [h]; rfl
    by_cases h' : i < eSteps x y
    · have := hne i h'
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', e, this]
      exact fun h => this (e.mp h)
    · have hi' : i = eSteps x y := by omega
      subst hi'
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e, hz]
  generalize hp : euS^[i] (x, y) = p
  obtain ⟨px, py⟩ := p
  have hpx : px < B := by have := (hlt i).1; rw [hp] at this; exact this
  have hpy : py < B := by have := (hlt i).2; rw [hp] at this; exact this
  have hpy0 : 0 < py := by have := hne i hi; rw [hp] at this; exact Nat.pos_of_ne_zero this
  have hsucc : euS^[i + 1] (x, y) = (py, px % py) := by rw [Function.iterate_succ_apply', hp]; rfl
  simp only [gcG, hp, hsucc]
  let Γ0 : Env := (dX, BitVec.ofNat 64 px) :: (dY, BitVec.ofNat 64 py) :: Γb
  refine step_seq (step_assignI dR (.const 0) (BitVec.ofNat 64 0) dr rfl) ?_
  refine step_seq (step_assignI dQ (.const 0) (BitVec.ofNat 64 0) dq rfl) ?_
  refine step_seq (step_assignI dI (.const 0) (BitVec.ofNat 64 0) di rfl) ?_
  have ht0 : topBits px 0 = 0 := topBits_0 px hpx
  refine step_seq (step_mono (wdiv_loop (Γ0 := Γ0) px py hpx hpy0 hpy ⟨ds, dc, dt, dr, dg', dq, di⟩
    (by simp [Γ0]) (by simp [Γ0]) (by simp [Γ0, hnS]) (by simp [Γ0, hnC]) (by simp [Γ0, hnT]) (by simp [Γ0, hnG]))
    (fun t ht => inv_envMono ht (fun z v hz => ?_)) (fun _ h => h)) ?_
  · simp only [wdG, Γ0, ht0, Nat.zero_mod, Nat.zero_div, Env.get_cons] at hz ⊢
    by_cases e1 : z = dI
    · subst e1; simpa using hz
    by_cases e2 : z = dR
    · subst e2; simpa using hz
    by_cases e3 : z = dQ
    · subst e3; simpa using hz
    simp only [e1, e2, e3, ite_false] at hz ⊢
    exact hz
  refine step_seq (step_assignI dX _ (BitVec.ofNat 64 py) dx (by simp [sev, wdG, Γ0])) ?_
  refine step_mono (step_assignI dY _ (BitVec.ofNat 64 (px % py)) dy (by simp [sev, wdG, Γ0, topBits_64]))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [Env.get_cons] at hz ⊢
  by_cases e1 : z = dX
  · subst e1; simpa using hz
  by_cases e2 : z = dY
  · subst e2; simpa using hz
  simp only [e1, e2, ite_false] at hz ⊢
  have f : ∀ w, Γb.get w = none → z ≠ w := fun w hw e => by subst e; rw [hw] at hz; simp at hz
  simp [wdG, Γ0, e1, e2, f _ hnS, f _ hnC, f _ hnT, f _ hnG, f _ hnI, f _ hnR, f _ hnQ, hz]

theorem blk_word {H : List (BitVec 64)} {o a : Nat} (hba : BlkAt H o (limbs a)) (h1 : (limbs a).length ≤ 1) :
    a < B ∧ H[o + (limbs a).length]? = some (BitVec.ofNat 64 a) := by
  have haB1 : a < B := by have := (limbs_length_lt_iff a 1).mp h1; simpa using this
  refine ⟨haB1, ?_⟩
  rcases (by omega : (limbs a).length = 0 ∨ (limbs a).length = 1) with h | h
  · have haz : a = 0 := by have := (limbs_length_lt_iff a 0).mp (by omega); simpa using this
    have := hba.1
    rw [h, Nat.add_zero, this, h, haz]
  · rw [h, show o + 1 = o + 1 + 0 by rfl, hba.2 0 (by omega), limbs_getElem a 0 (by omega)]
    simp only [Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt haB1]

theorem gcd_spec (C : Ctx) (hok : CtxOK C) (s : AState) (a b : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs a)) (hbb : BlkAt C.H ob (limbs b)) :
    SpecR (σ := σ) (Pre C s (dmParams.zip [cellA C oa, cellA C ob])) (gcdBody C) s
      (pure (Nat.gcd a b) : AM Nat) (PostH C s) := by
  refine specR_prologue (postH_locals C s) (dm_none C _) ?_
  unfold gcdCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs a).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs b).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' rLa (vv rX) oa _ hla0 (by decide) (by simp +decide [Env.get, dmParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' rLb (vv rY) ob _ hlb0 (by decide) (by simp +decide [Env.get, dmParams, ctxEnv]) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  obtain ⟨H0, hp0, ha0⟩ := ht0.sr.heap
  have hbl := blkAt_len hba
  have hbl2 := blkAt_len hbb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  have hwa := word_lt_iff 1 (limbs a).length (by decide) (by unfold B; omega)
  have hwb := word_lt_iff 1 (limbs b).length (by decide) (by unfold B; omega)
  by_cases ha1 : 1 < (limbs a).length
  · exact specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwa.mpr ha1])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hwa).mpr ha1])
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hb1 : 1 < (limbs b).length
  · exact specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwb.mpr hb1])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hwb).mpr hb1])
    (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨haB, haw⟩ := blk_word hba (by omega)
  obtain ⟨hbB, hbw⟩ := blk_word hbb (by omega)
  refine UD.specR_heapLoadI' dX _ (oa + (limbs a).length) _ haw (by decide) (by
    simp +decide [sev, Env.get, dmParams, ctxEnv]
    have m8 : BitVec.ofNat 64 (limbs a).length * 8#64 = BitVec.ofNat 64 (8 * (limbs a).length) := CV.mul8_eq _
    rw [m8]
    unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega) ?_
  refine UD.specR_heapLoadI' dY _ (ob + (limbs b).length) _ hbw (by decide) (by
    simp +decide [sev, Env.get, dmParams, ctxEnv]
    have m8 : BitVec.ofNat 64 (limbs b).length * 8#64 = BitVec.ofNat 64 (8 * (limbs b).length) := CV.mul8_eq _
    rw [m8]
    unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega) ?_
  refine specR_envWeak (Γb := gcG [] (a, b) 0) (fun z v hz => ?_) ?_
  · simp only [gcG, Function.iterate_zero, id, Env.get_cons] at hz ⊢
    by_cases e1 : z = dX
    · subst e1; simpa using hz
    by_cases e2 : z = dY
    · subst e2; simpa using hz
    simp [e1, e2, Env.get] at hz
  refine gcd_loop a b haB hbB (by decide) rfl rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨-, -, hg⟩ := eu_facts b a
  have hlt := (eu_lt B (eSteps a b) (a, b) haB hbB).1
  rw [hg] at hlt
  exact wordBlk_spec hok (Nat.gcd a b) hlt (by simp [gcG, hg]) (by decide) (by decide)

end

end ConPanqueque.T.Big
