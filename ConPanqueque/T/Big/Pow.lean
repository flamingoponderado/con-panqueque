import ConPanqueque.T.Big.Shl
import ConPanqueque.T.Big.Div
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Nat.pow`

`pow(a, e)` for a word `e`, recursively: `e = 0` answers `1`; otherwise `h = pow(a, e / 2)`, `h * h`, times `a`
when `e` is odd — each product by the verified `bigMul`. The recursion is at most 64 deep.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def pwX := ofString "wpx"
def pwE := ofString "wpe"
def pwH := ofString "wph"
def pwS := ofString "wps"
def pwR := ofString "wpr"
def pwO := ofString "wpo"
def fPow := ofString "bigPow"

@[simp] theorem pwX_ne_pwE : pwX ≠ pwE := by decide
@[simp] theorem pwX_ne_pwH : pwX ≠ pwH := by decide
@[simp] theorem pwX_ne_pwS : pwX ≠ pwS := by decide
@[simp] theorem pwX_ne_pwR : pwX ≠ pwR := by decide
@[simp] theorem pwX_ne_pwO : pwX ≠ pwO := by decide
@[simp] theorem pwE_ne_pwX : pwE ≠ pwX := by decide
@[simp] theorem pwE_ne_pwH : pwE ≠ pwH := by decide
@[simp] theorem pwE_ne_pwS : pwE ≠ pwS := by decide
@[simp] theorem pwE_ne_pwR : pwE ≠ pwR := by decide
@[simp] theorem pwE_ne_pwO : pwE ≠ pwO := by decide
@[simp] theorem pwH_ne_pwX : pwH ≠ pwX := by decide
@[simp] theorem pwH_ne_pwE : pwH ≠ pwE := by decide
@[simp] theorem pwH_ne_pwS : pwH ≠ pwS := by decide
@[simp] theorem pwH_ne_pwR : pwH ≠ pwR := by decide
@[simp] theorem pwH_ne_pwO : pwH ≠ pwO := by decide
@[simp] theorem pwS_ne_pwX : pwS ≠ pwX := by decide
@[simp] theorem pwS_ne_pwE : pwS ≠ pwE := by decide
@[simp] theorem pwS_ne_pwH : pwS ≠ pwH := by decide
@[simp] theorem pwS_ne_pwR : pwS ≠ pwR := by decide
@[simp] theorem pwS_ne_pwO : pwS ≠ pwO := by decide
@[simp] theorem pwR_ne_pwX : pwR ≠ pwX := by decide
@[simp] theorem pwR_ne_pwE : pwR ≠ pwE := by decide
@[simp] theorem pwR_ne_pwH : pwR ≠ pwH := by decide
@[simp] theorem pwR_ne_pwS : pwR ≠ pwS := by decide
@[simp] theorem pwR_ne_pwO : pwR ≠ pwO := by decide
@[simp] theorem pwO_ne_pwX : pwO ≠ pwX := by decide
@[simp] theorem pwO_ne_pwE : pwO ≠ pwE := by decide
@[simp] theorem pwO_ne_pwH : pwO ≠ pwH := by decide
@[simp] theorem pwO_ne_pwS : pwO ≠ pwS := by decide
@[simp] theorem pwO_ne_pwR : pwO ≠ pwR := by decide

section
variable {σ : Type}

/-- Calling a helper whose spec answers a fresh limb block for `n`. -/
theorem specR_callPH {β : Type} {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {k : Nat → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64)) (n : Nat)
    (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (σ := σ) (Pre C s (ps.zip vs)) Bd s (pure n : AM Nat) (PostH C s))
    (hk : ∀ H' o, C.H <+: H' → BlkAt H' o (limbs n) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s (k n) R) :
    SpecR (Inv C s Γ [] D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (k n) R := by
  refine specR_congr (m' := (pure n : AM Nat) >>= k) rfl ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes
    (fun tt w s' st => (pure n : AM Nat) s = .ok (tt, s') ∧ PostH C s tt w s' st)
    (fun tt w s' H2 => tt = n ∧ s' = s ∧ ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (limbs tt))
    (fun tt w s' st ⟨hrun, H2, o2, hp, hw, hb, hs, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨H2, hp, ⟨rfl, hs, o2, hw, hb⟩, hs ▸ hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec))
    (fun tt w s' H2 hp2 ⟨htt, hs, o2, hw, hb2⟩ => ?_)
  subst htt hs hw
  exact hk H2 o2 hp2 hb2

def oneBlk (C : Ctx) : ProgHOL 64 :=
  allocP C pwO (.const 16) (.seq (.store (vv pwO) (.const 1))
    (.seq (.store (.op .add [vv pwO, .const 8]) (.const 1)) (.return (vv pwO))))

def powCore : ProgHOL 64 :=
  .seq (.call (some (some (.local, pwH), none)) fPow [vv pwX, .shift .lsr (vv pwE) (.const 1)])
  (.seq (.call (some (some (.local, pwS), none)) fMul [vv pwH, vv pwH])
  (.ite (.op .and [vv pwE, .const 1])
    (.seq (.call (some (some (.local, pwR), none)) fMul [vv pwS, vv pwX]) (.return (vv pwR)))
    (.return (vv pwS))))

def powLocals : List MlS := [pwH, pwS, pwR, pwO]
def powParams : List MlS := [pwX, pwE]
def powBody (C : Ctx) : ProgHOL 64 :=
  prologue powLocals (.ite (.cmp .equal (vv pwE) (.const 0)) (oneBlk C) powCore)

theorem pow_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ powLocals → (ctxEnv C ++ powParams.zip vals).get x = none :=
  Knot.params_none C powLocals powParams vals (by decide) (by decide)

theorem oneBlk_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (hz : pwO ∈ D) :
    SpecR (σ := σ) (Inv C s Γ [] D) (oneBlk C) s (pure 1 : AM Nat) (PostH C s) := by
  unfold oneBlk
  refine specR_allocI pwO (.const 16) 2 (by norm_num) hz (fun v => by simp [sev]) (fun H' ws hpre hwl hcap => ?_)
  have hj : H'.length < (ctxH C (H' ++ ws)).H.length := by show _ < (H' ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv pwO) (.const 1) _ hj 1 (by simp; rfl) rfl ?_
  have hj2 : H'.length + 1 < (ctxH C ((H' ++ ws).set H'.length 1)).H.length := by
    show _ < ((H' ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (.const 1) _ hj2 1 (by simp [sev]; exact cellA_add8 C _) rfl ?_
  refine specR_returnI _ (cellA C H'.length) (by simp) (fun t ht => ?_)
  have hp1 := prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpre.length_le (1 : BitVec 64)
  have hp2 := prefix_set_ge hp1 (H'.length + 1) (by have := hpre.length_le; omega) (1 : BitVec 64)
  refine ⟨_, H'.length, hp2, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; rfl
  · have : i = 0 := by simpa using hi
    subst this
    show (((H' ++ ws).set H'.length 1).set (H'.length + 1) 1)[H'.length + 1 + 0]? = _
    rw [List.getElem?_set_self (by simp; omega)]; rfl

theorem pow_split (a e : Nat) : a ^ e = a ^ (e / 2) * a ^ (e / 2) * (if e % 2 = 1 then a else 1) := by
  conv_lhs => rw [← Nat.div_add_mod e 2]
  rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two, Nat.mul_pow]
  rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h]

theorem blk_small {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (hsr : SR C s t) {o n : Nat}
    (hb : BlkAt C.H o (limbs n)) : (limbs n).length < 2 ^ 58 := by
  obtain ⟨H0, hp0, ha0⟩ := hsr.heap
  have hbl := blkAt_len hb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  omega

theorem pow_spec (e : Nat) : ∀ (C : Ctx) (hok : CtxOK C) (s : AState) (a oa : Nat)
    (hcm : C.code.lookup fMul = some (mulParams.map (fun p => (p, ShapeHOL.one)), mulBody C, .one))
    (hcp : C.code.lookup fPow = some (powParams.map (fun p => (p, ShapeHOL.one)), powBody C, .one))
    (hba : BlkAt C.H oa (limbs a)) (he : e < B),
    SpecR (σ := σ) (Pre C s (powParams.zip [cellA C oa, BitVec.ofNat 64 e])) (powBody C) s
      (pure (a ^ e) : AM Nat) (PostH C s) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro C hok s a oa hcm hcp hba he
  refine specR_prologue (postH_locals C s) (pow_none C _) ?_
  by_cases e0 : e = 0
  · subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, powParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [Nat.pow_zero]; exact oneBlk_spec hok (by decide)
  have heB : e < 2 ^ 64 := he
  have hew : BitVec.ofNat 64 e ≠ 0 := fun h => e0 (by have := congrArg BitVec.toNat h; simp at this; omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, powParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hew)
    (fun h => absurd rfl h) (fun _ => ?_)
  unfold powCore
  refine specR_congr (m' := (fun h => (pure (h * h) : AM Nat) >>= fun _ => (pure (a ^ e) : AM Nat)) (a ^ (e / 2)))
    rfl ?_
  refine specR_callPH (k := fun h => (pure (h * h) : AM Nat) >>= fun _ => (pure (a ^ e) : AM Nat))
    pwH fPow powParams _ (powBody C) [cellA C oa, BitVec.ofNat 64 (e / 2)] (a ^ (e / 2)) (by decide) rfl (by decide)
    hcp ⟨by simp +decide [sev, Env.get, powParams, ctxEnv], by
      simp +decide [sev, Env.get, powParams, ctxEnv]
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt heB]; omega, trivial⟩
    (ih (e / 2) (by omega) C hok s a oa hcm hcp hba (by unfold B; omega)) (fun H1 o1 hp1 hb1 => ?_)
  refine specR_atEntry fun t1 ht1 => ?_
  have hl1 : (limbs (a ^ (e / 2))).length < 2 ^ 58 := blk_small (C := ctxH C H1) (ctxOK_H hok _) ht1.sr hb1
  refine specR_callPH (C := ctxH C H1) (k := fun _ => (pure (a ^ e) : AM Nat))
    pwS fMul mulParams _ (mulBody C) [cellA C o1, cellA C o1] (a ^ (e / 2) * a ^ (e / 2)) (by decide) rfl (by decide)
    hcm ⟨by simp [sev], by simp [sev], trivial⟩
    (mul_spec (ctxH C H1) (ctxOK_H hok _) s _ _ o1 o1 hb1 hb1 (by omega)) (fun H2 o2 hp2 hb2 => ?_)
  have hsplit := pow_split a e
  have hand : BitVec.ofNat 64 e &&& 1#64 = BitVec.ofNat 64 (e % 2) := by
    apply BitVec.eq_of_toNat_eq
    have e1 : (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
    simp only [BitVec.toNat_and, e1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt heB]
    omega
  rcases Nat.mod_two_eq_zero_or_one e with hodd | hodd
  · refine specR_ifI _ (BitVec.ofNat 64 (e % 2)) (by simp +decide [sev, Env.get, powParams, ctxEnv]; exact hand)
      (fun h => absurd (by rw [hodd]; rfl) h) (fun _ => ?_)
    refine specR_returnI _ (cellA C o2) (by simp [sev]; rfl) (fun t ht => ?_)
    rw [hodd] at hsplit
    simp only [show (0 : Nat) ≠ 1 from by decide, ite_false, Nat.mul_one] at hsplit
    rw [hsplit]
    exact ⟨H2, o2, hp1.trans hp2, rfl, hb2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · refine specR_ifI _ (BitVec.ofNat 64 (e % 2)) (by simp +decide [sev, Env.get, powParams, ctxEnv]; exact hand)
      (fun _ => ?_) (fun h => absurd h (by rw [hodd]; decide))
    refine specR_atEntry fun t2 ht2 => ?_
    have hl2 := blk_small (C := ctxH C H2) (ctxOK_H hok _) ht2.sr hb2
    have hba2 : BlkAt H2 oa (limbs a) := blkAt_mono hba (hp1.trans hp2)
    have hla := blk_small (C := ctxH C H2) (ctxOK_H hok _) ht2.sr hba2
    refine specR_callPH (C := ctxH C H2) (k := fun _ => (pure (a ^ e) : AM Nat))
      pwR fMul mulParams _ (mulBody C) [cellA C o2, cellA C oa] (a ^ (e / 2) * a ^ (e / 2) * a) (by decide) rfl
      (by decide) hcm ⟨by simp [sev]; rfl, by simp +decide [sev, Env.get, powParams, ctxEnv], trivial⟩
      (mul_spec (ctxH C H2) (ctxOK_H hok _) s _ _ o2 oa hb2 hba2 (by omega)) (fun H3 o3 hp3 hb3 => ?_)
    refine specR_returnI _ (cellA C o3) (by simp [sev]; rfl) (fun t ht => ?_)
    rw [hodd] at hsplit
    simp only [ite_true] at hsplit
    rw [hsplit]
    exact ⟨H3, o3, hp1.trans (hp2.trans hp3), rfl, hb3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.Big
