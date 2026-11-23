import ConPanqueque.T.Big.Shr
import ConPanqueque.T.Big.WDivMath
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Dividing one word by another

Pancake has no division: `wdivLoop` is 64 restoring steps. Bit `63 - i` of `x` enters the remainder; the
step subtracts `y` when the doubled remainder reaches it (the bit shifted out, or a comparison).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex

def dX := ofString "dqx"
def dY := ofString "dqy"
def dR := ofString "dqr"
def dQ := ofString "dqq"
def dI := ofString "dqi"
def dC := ofString "dqc"
def dT := ofString "dqt"
def dG := ofString "dqg"
def dS := ofString "dqs"

@[simp] theorem dX_ne_dY : dX ≠ dY := by decide
@[simp] theorem dX_ne_dR : dX ≠ dR := by decide
@[simp] theorem dX_ne_dQ : dX ≠ dQ := by decide
@[simp] theorem dX_ne_dI : dX ≠ dI := by decide
@[simp] theorem dX_ne_dC : dX ≠ dC := by decide
@[simp] theorem dX_ne_dT : dX ≠ dT := by decide
@[simp] theorem dX_ne_dG : dX ≠ dG := by decide
@[simp] theorem dX_ne_dS : dX ≠ dS := by decide
@[simp] theorem dY_ne_dX : dY ≠ dX := by decide
@[simp] theorem dY_ne_dR : dY ≠ dR := by decide
@[simp] theorem dY_ne_dQ : dY ≠ dQ := by decide
@[simp] theorem dY_ne_dI : dY ≠ dI := by decide
@[simp] theorem dY_ne_dC : dY ≠ dC := by decide
@[simp] theorem dY_ne_dT : dY ≠ dT := by decide
@[simp] theorem dY_ne_dG : dY ≠ dG := by decide
@[simp] theorem dY_ne_dS : dY ≠ dS := by decide
@[simp] theorem dR_ne_dX : dR ≠ dX := by decide
@[simp] theorem dR_ne_dY : dR ≠ dY := by decide
@[simp] theorem dR_ne_dQ : dR ≠ dQ := by decide
@[simp] theorem dR_ne_dI : dR ≠ dI := by decide
@[simp] theorem dR_ne_dC : dR ≠ dC := by decide
@[simp] theorem dR_ne_dT : dR ≠ dT := by decide
@[simp] theorem dR_ne_dG : dR ≠ dG := by decide
@[simp] theorem dR_ne_dS : dR ≠ dS := by decide
@[simp] theorem dQ_ne_dX : dQ ≠ dX := by decide
@[simp] theorem dQ_ne_dY : dQ ≠ dY := by decide
@[simp] theorem dQ_ne_dR : dQ ≠ dR := by decide
@[simp] theorem dQ_ne_dI : dQ ≠ dI := by decide
@[simp] theorem dQ_ne_dC : dQ ≠ dC := by decide
@[simp] theorem dQ_ne_dT : dQ ≠ dT := by decide
@[simp] theorem dQ_ne_dG : dQ ≠ dG := by decide
@[simp] theorem dQ_ne_dS : dQ ≠ dS := by decide
@[simp] theorem dI_ne_dX : dI ≠ dX := by decide
@[simp] theorem dI_ne_dY : dI ≠ dY := by decide
@[simp] theorem dI_ne_dR : dI ≠ dR := by decide
@[simp] theorem dI_ne_dQ : dI ≠ dQ := by decide
@[simp] theorem dI_ne_dC : dI ≠ dC := by decide
@[simp] theorem dI_ne_dT : dI ≠ dT := by decide
@[simp] theorem dI_ne_dG : dI ≠ dG := by decide
@[simp] theorem dI_ne_dS : dI ≠ dS := by decide
@[simp] theorem dC_ne_dX : dC ≠ dX := by decide
@[simp] theorem dC_ne_dY : dC ≠ dY := by decide
@[simp] theorem dC_ne_dR : dC ≠ dR := by decide
@[simp] theorem dC_ne_dQ : dC ≠ dQ := by decide
@[simp] theorem dC_ne_dI : dC ≠ dI := by decide
@[simp] theorem dC_ne_dT : dC ≠ dT := by decide
@[simp] theorem dC_ne_dG : dC ≠ dG := by decide
@[simp] theorem dC_ne_dS : dC ≠ dS := by decide
@[simp] theorem dT_ne_dX : dT ≠ dX := by decide
@[simp] theorem dT_ne_dY : dT ≠ dY := by decide
@[simp] theorem dT_ne_dR : dT ≠ dR := by decide
@[simp] theorem dT_ne_dQ : dT ≠ dQ := by decide
@[simp] theorem dT_ne_dI : dT ≠ dI := by decide
@[simp] theorem dT_ne_dC : dT ≠ dC := by decide
@[simp] theorem dT_ne_dG : dT ≠ dG := by decide
@[simp] theorem dT_ne_dS : dT ≠ dS := by decide
@[simp] theorem dG_ne_dX : dG ≠ dX := by decide
@[simp] theorem dG_ne_dY : dG ≠ dY := by decide
@[simp] theorem dG_ne_dR : dG ≠ dR := by decide
@[simp] theorem dG_ne_dQ : dG ≠ dQ := by decide
@[simp] theorem dG_ne_dI : dG ≠ dI := by decide
@[simp] theorem dG_ne_dC : dG ≠ dC := by decide
@[simp] theorem dG_ne_dT : dG ≠ dT := by decide
@[simp] theorem dG_ne_dS : dG ≠ dS := by decide
@[simp] theorem dS_ne_dX : dS ≠ dX := by decide
@[simp] theorem dS_ne_dY : dS ≠ dY := by decide
@[simp] theorem dS_ne_dR : dS ≠ dR := by decide
@[simp] theorem dS_ne_dQ : dS ≠ dQ := by decide
@[simp] theorem dS_ne_dI : dS ≠ dI := by decide
@[simp] theorem dS_ne_dC : dS ≠ dC := by decide
@[simp] theorem dS_ne_dT : dS ≠ dT := by decide
@[simp] theorem dS_ne_dG : dS ≠ dG := by decide

def wdivLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv dI) (.const 64))
    (.seq (.assign .local dS (.op .sub [.const 63, vv dI]))
    (.seq (.assign .local dC (.shift .lsr (vv dR) (.const 63)))
    (.seq (.assign .local dT (.op .and [.shift .lsr (vv dX) (vv dS), .const 1]))
    (.seq (.assign .local dR (.op .add [.shift .lsl (vv dR) (.const 1), vv dT]))
    (.seq (.assign .local dG (.op .or [vv dC, .op .xor [.cmp .lower (vv dR) (vv dY), .const 1]]))
    (.seq (.assign .local dR (.op .sub [vv dR, .panop .mul [vv dG, vv dY]]))
    (.seq (.assign .local dQ (.op .add [.shift .lsl (vv dQ) (.const 1), vv dG]))
    (.assign .local dI (.op .add [vv dI, .const 1])))))))))

theorem bit_word (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 64) :
    (BitVec.ofNat 64 x >>> (BitVec.ofNat 64 (63 - k)).toNat) &&& 1 = BitVec.ofNat 64 (x / 2 ^ (63 - k) % 2) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 (63 - k)).toNat = 63 - k := by simp; omega
  have e1 : (1 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, e1, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem quo_word (Q g : Nat) (h : 2 * Q + g < 2 ^ 64) :
    (BitVec.ofNat 64 Q <<< (1 : Nat)) + BitVec.ofNat 64 g = BitVec.ofNat 64 (2 * Q + g) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show Q < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show g < 2 ^ 64 by omega)]
  omega

theorem topBits_lt (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64) : topBits x k < 2 ^ k := by
  unfold topBits
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show k + (64 - k) = 64 by omega]
  exact hx

def wdG (Γ0 : Env) (x y k : Nat) : Env :=
  (dI, BitVec.ofNat 64 k) :: (dR, BitVec.ofNat 64 (topBits x k % y)) ::
    (dQ, BitVec.ofNat 64 (topBits x k / y)) :: Γ0

section
variable {σ : Type}

theorem wdiv_loop {C : Ctx} {s : AState} {M : Mem} {D : List MlS} {Γ0 : Env} (x y : Nat)
    (hx : x < B) (hy0 : 0 < y) (hy : y < B)
    (hD : dS ∈ D ∧ dC ∈ D ∧ dT ∈ D ∧ dR ∈ D ∧ dG ∈ D ∧ dQ ∈ D ∧ dI ∈ D)
    (hX : Γ0.get dX = some (BitVec.ofNat 64 x)) (hY : Γ0.get dY = some (BitVec.ofNat 64 y))
    (hnS : Γ0.get dS = none) (hnC : Γ0.get dC = none) (hnT : Γ0.get dT = none) (hnG : Γ0.get dG = none) :
    Step (Inv (σ := σ) C s (wdG Γ0 x y 0) M D) wdivLoop (Inv C s (wdG Γ0 x y 64) M D) := by
  obtain ⟨ds, dc, dt, dr, dg', dq, di⟩ := hD
  have hB : B = 2 ^ 64 := rfl
  rw [hB] at hx hy
  refine step_forI (σ := σ) _ _ 64 (fun _ => C) (wdG Γ0 x y)
    (fun k hk => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 k) (BitVec.ofNat 64 64)
      then 1 else 0, by simp [sev, wdG, Env.get], ?_⟩) (fun k hk => ?_)
  · have e := word_lt_iff k 64 (by unfold B; omega) (by unfold B; omega)
    by_cases h' : k < 64
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 k < BitVec.ofNat 64 64 := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  simp only [wdG]
  generalize hT : topBits x k = T
  have hTl : T < 2 ^ k := hT ▸ topBits_lt x k hx (by omega)
  have hR : T % y < y := Nat.mod_lt _ hy0
  generalize hbit : x / 2 ^ (63 - k) % 2 = bit
  have hb : bit < 2 := by omega
  obtain ⟨hq1, hr1⟩ := divmod_step T y bit hy0 hb
  have hW := wdiv_word (T % y) y bit hR (by unfold B; omega) hb
  dsimp only at hW
  obtain ⟨hge, hsub⟩ := hW
  refine step_seq (step_assignI dS _ (BitVec.ofNat 64 (63 - k)) ds ?_) ?_
  · simp [sev, wdG, Env.get_cons]
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 63 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  refine step_seq (step_assignI dC _ (BitVec.ofNat 64 (T % y) >>> 63) dc (by simp [sev, wdG])) ?_
  refine step_seq (step_assignI dT _ (BitVec.ofNat 64 bit) dt ?_) ?_
  · simp [sev, vv, hX]
    rw [Nat.mod_eq_of_lt (show 63 - k < 18446744073709551616 by omega)]
    have := bit_word x k hx (by omega)
    rw [show (BitVec.ofNat 64 (63 - k)).toNat = 63 - k by simp; omega] at this
    rw [← hbit, ← this, if_pos (by omega)]; rfl
  refine step_seq (step_assignI dR _ ((BitVec.ofNat 64 (T % y) <<< 1) + BitVec.ofNat 64 bit) dr
    (by simp [sev, wdG])) ?_
  refine step_seq (step_assignI dG _ (BitVec.ofNat 64 (if y ≤ 2 * (T % y) + bit then 1 else 0)) dg' ?_) ?_
  · rw [← hge]; simp [sev, wdG, hY, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine step_seq (step_assignI dR _ (BitVec.ofNat 64 ((2 * T + bit) % y)) dr ?_) ?_
  · rw [hr1, ← hsub, hge]; simp [sev, wdG, hY]
  have hq' : 2 * (T / y) + (if y ≤ 2 * (T % y) + bit then 1 else 0) < 2 ^ 64 := by
    rw [← hq1]
    have : 2 * T + bit < 2 ^ 64 := by
      have : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this
  refine step_seq (step_assignI dQ _ (BitVec.ofNat 64 ((2 * T + bit) / y)) dq ?_) ?_
  · rw [hq1, ← quo_word _ _ hq']; simp [sev, wdG]
  refine step_mono (step_assignI dI _ (BitVec.ofNat 64 (k + 1)) di (by simp [sev, wdG]; exact word_add1_eq k))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  have hT1 : topBits x (k + 1) = 2 * T + bit := by rw [topBits_succ x k (by omega), hT, hbit]
  simp only [wdG, Env.get_cons, hT1] at hz ⊢
  by_cases e1 : z = dI
  · subst e1; simp_all
  by_cases e2 : z = dR
  · subst e2; simp_all
  by_cases e3 : z = dQ
  · subst e3; simp_all
  simp only [e1, e2, e3, ite_false] at hz
  have f : ∀ w, Γ0.get w = none → z ≠ w := fun w hw e => by subst e; rw [hw] at hz; simp at hz
  simp [e1, e2, e3, f _ hnS, f _ hnC, f _ hnT, f _ hnG, hz]

theorem topBits_64 (x : Nat) : topBits x 64 = x := by simp [topBits]
theorem topBits_0 (x : Nat) (hx : x < 2 ^ 64) : topBits x 0 = 0 := by
  unfold topBits; exact Nat.div_eq_of_lt hx

end

end ConPanqueque.T.Big
