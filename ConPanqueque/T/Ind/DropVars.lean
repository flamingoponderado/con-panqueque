import ConPanqueque.T.Ind.IotaMinors
import ConPanqueque.T.Ex.Inst1Fast
import ConPanqueque.T.EIntern2

/-!
# `exprDropVars`: drop the `n` innermost variables

Each step instantiates the innermost variable with `Sort 0` (`internSortE`, `instantiate1Fast`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI

def dvN := ofString "dv_n"
def dvE := ofString "dv_e"
def dvZ := ofString "dv_z"
def dvS := ofString "dv_s"
def dvX := ofString "dv_x"
def fDropVars := ofString "dropVars"

def dvParams : List MlS := [dvN, dvE]
def dvLocals : List MlS := [dvZ, dvS, dvX]

def dvBody (C : Ctx) : ProgHOL 64 := prologue dvLocals
  (.ite (.cmp .equal (vv dvN) (.const 0)) (.return (vv dvE))
    (.seq (.assign .local dvZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, dvS), none)) fInternSort [vv dvZ])
    (.seq (.call (some (some (.local, dvX), none)) fInst1F [.const (BitVec.ofNat 64 coreWalkFuel), vv dvE, vv dvS, .const 0])
    (.seq (.call (some (some (.local, dvX), none)) fDropVars [.op .sub [vv dvN, .const 1], vv dvX])
      (.return (vv dvX)))))))

section
variable {σ : Type}

theorem dv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dvLocals → (ctxEnv C ++ dvParams.zip vals).get x = none :=
  Knot.params_none C dvLocals dvParams vals (by decide) (by decide)

theorem dv_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (body C)) :
    ∀ n, n < 2 ^ 64 → ∀ (s : AState) (e : EIdx),
      SpecR (σ := σ) (Pre C s (dvParams.zip [BitVec.ofNat 64 n, Enc.idxW e])) (dvBody C) s (exprDropVars n e)
        (PostE C) := by
  intro n
  induction n with
  | zero =>
    intro _ s e
    refine specR_prologue (postE_locals C) (dv_none _ _) ?_
    rw [exprDropVars]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ _ (by simp +decide [sev, Env.get, dvParams, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro hn s e
    refine specR_prologue (postE_locals C) (dv_none _ _) ?_
    rw [exprDropVars]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hn
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, dvParams, ctxEnv] at hw; exact absurd hw this
    simp only [zeroLevel, bind_assoc]
    refine specR_pinXI hok pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hok hp)
      (pin_zeroLevel_cell hok) dvZ (by simp +decide [ctxLocals, dvLocals]) ?_
    refine ILP.callE_spec dvS fInternSort [lEu] [vv dvZ] sortBody [Enc.idxW C.pins.zeroLevel] (by decide) rfl
      (by simp +decide [ctxLocals, dvLocals]) hcS ⟨by simp [sev, Env.get_cons], trivial⟩
      (sort_body_spec ra C hok s C.pins.zeroLevel) (fun s0 s1 => ?_)
    refine ILP.callE_spec dvX fInst1F [pFu, pH, pV, pD] [.const (BitVec.ofNat 64 coreWalkFuel), vv dvE, vv dvS, .const 0]
      (fastBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, Enc.idxW s0, BitVec.ofNat 64 0] (by decide) rfl
      (by simp +decide [ctxLocals, dvLocals]) hcF
      ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, dvParams, ctxEnv], by simp [sev, Env.get_cons], rfl, trivial⟩
      (fast_spec ra C hok hcI s1 coreWalkFuel e s0 0 (by decide) (by decide)) (fun e1 s2 => ?_)
    refine specR_congr (m' := exprDropVars n e1 >>= fun r => pure r) (by simp) ?_
    refine ILP.callE_spec dvX fDropVars dvParams [.op .sub [vv dvN, .const 1], vv dvX] (dvBody C)
      [BitVec.ofNat 64 n, Enc.idxW e1] (by decide) rfl (by simp +decide [ctxLocals, dvLocals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dvParams, ctxEnv]; exact ofNat_succ_sub_one n,
        by simp [sev, Env.get_cons], trivial⟩
      (ih (by omega) s2 e1) (fun r s3 => ?_)
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
