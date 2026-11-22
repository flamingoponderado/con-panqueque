import ConPanqueque.T.Ex.Inst1
import ConPanqueque.T.MemoClear
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `instantiate1Fast`: the walk's top-level entry

The memo is fresh before the walk and dropped after (`inst1Clear`), because it depends on the
substituted term.
-/

namespace ConPanqueque.T.ExI
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS

def fInst1F := ofString "instantiate1"
def fastLocals : List MlS := [lJ0, lW]

def fastBody (C : Ctx) : ProgHOL 64 :=
  prologue fastLocals (clearCode C.mg
    (.seq (.call (some (some (.local, lW), none)) fInst1 [vv pV, vv pFu, vv pH, vv pD])
      (clearCode C.mg (.return (vv lW)))))

section
variable {σ : Type}

theorem fast_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : Codes C (body C))
    (s : AState) (fuel : Nat) (e v : EIdx) (d : Nat) (hf : fuel < 2 ^ 64) (hd : d < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pH, Enc.idxW e), (pV, Enc.idxW v), (pD, BitVec.ofNat 64 d)])
      (fastBody C) s (instantiate1Fast fuel e v d) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fastLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  refine specR_inst1ClearI hok (by decide) ?_
  refine specR_call4IM lW fInst1 pV pFu pH pD (by decide) _ _ _ _ (body C) (Enc.idxW v) (BitVec.ofNat 64 fuel)
    (Enc.idxW e) (BitVec.ofNat 64 d) (by decide) hc.inst1 (by simp +decide [Env.kill, ctxEnv])
    (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact inst1_spec ra C hok hc fuel hf v e d _ hd _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · simp at hy⟩)
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, _⟩ := hp
  refine specR_inst1ClearI hok (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExI
