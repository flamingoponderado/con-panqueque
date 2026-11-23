import ConPanqueque.T.Core.PeelPis
import ConPanqueque.T.Big.LitCopyG
import ConPanqueque.T.Str.Utf8
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Interning a one-word `Nat` literal

`litWord(v)`: the block `[v ≠ 0, v]` (that is `limbs v` with a spare cell when `v = 0`), then `litBlk`.
-/

namespace ConPanqueque.T.Str

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

def wV := ofString "lwv"
def wO := ofString "lwo"
def wR := ofString "lwr"
def fLitW := ofString "litWord"

@[simp] theorem lw_wV_ne_wO : wV ≠ wO := by decide
@[simp] theorem lw_wV_ne_wR : wV ≠ wR := by decide
@[simp] theorem lw_wO_ne_wV : wO ≠ wV := by decide
@[simp] theorem lw_wO_ne_wR : wO ≠ wR := by decide
@[simp] theorem lw_wR_ne_wV : wR ≠ wV := by decide
@[simp] theorem lw_wR_ne_wO : wR ≠ wO := by decide

def lwLocals : List MlS := [wO, wR]

def lwBody (C : Ctx) : ProgHOL 64 :=
  prologue lwLocals
  (allocP C wO (.const 16) (.seq (.store (vv wO) (.cmp .notEqual (vv wV) (.const 0)))
  (.seq (.store (.op .add [vv wO, .const 8]) (vv wV))
  (.seq (.call (some (some (.local, wR), none)) fLitB [vv wO]) (.return (vv wR))))))

section
variable {σ : Type}

theorem lw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lwLocals → (ctxEnv C ++ [wV].zip vals).get x = none :=
  Knot.params_none C lwLocals [wV] vals (by decide) (by decide)

theorem lw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcb : C.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C, .one)) (s : AState) (v : Nat) (hv : v < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s [(wV, BitVec.ofNat 64 v)]) (lwBody C) s (internE (.lit (.natVal v))) (Knot.PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (lw_none C [BitVec.ofNat 64 v]) ?_
  refine specR_allocI wO (.const 16) 2 (by norm_num) (by decide) (fun _ => by simp [sev])
    (fun H3 ws hpre hwl hcap => ?_)
  have hpl := hpre.length_le
  let w0 : BitVec 64 := if v = 0 then 0 else 1
  have hj : H3.length < (ctxH C (H3 ++ ws)).H.length := by show _ < (H3 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv wO) _ _ hj w0 (by simp; rfl)
    (by
      simp only [sev, sev_vv, Env.get_cons, ne_eq, show wV ≠ wO by decide, not_false_eq_true, ite_false]
      simp +decide [Env.get, ctxEnv, w0]
      by_cases h0 : v = 0
      · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      · have : BitVec.ofNat 64 v ≠ 0 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h0]; exact this) ?_
  have hj2 : H3.length + 1 < (ctxH C ((H3 ++ ws).set H3.length w0)).H.length := by
    show _ < ((H3 ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (vv wV) _ hj2 (BitVec.ofNat 64 v) (by simp [sev]; exact cellA_add8 C _)
    (by simp +decide [Env.get, ctxEnv]) ?_
  let H4 := ((H3 ++ ws).set H3.length w0).set (H3.length + 1) (BitVec.ofNat 64 v)
  have hp1' := prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpl w0
  have hp2' : C.H <+: H4 := prefix_set_ge hp1' (H3.length + 1) (by omega) _
  have hbo : BlkAt H4 H3.length (Enc.limbs v) := by
    rw [limbs_word v hv]
    by_cases h0 : v = 0
    · subst h0
      refine ⟨?_, fun i hi => by simp at hi⟩
      show (((H3 ++ ws).set H3.length w0).set (H3.length + 1) _)[H3.length]? = _
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; simp [w0]
    · rw [if_neg h0]
      refine ⟨?_, fun i hi => ?_⟩
      · show (((H3 ++ ws).set H3.length w0).set (H3.length + 1) _)[H3.length]? = _
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; simp [w0, h0]
      · have : i = 0 := by simpa using hi
        subst this
        show (((H3 ++ ws).set H3.length w0).set (H3.length + 1) _)[H3.length + 1 + 0]? = _
        rw [List.getElem?_set_self (by simp; omega)]; rfl
  refine specR_congr (m' := internE (.lit (.natVal v)) >>= fun r => pure r) (by simp) ?_
  refine specR_callKH (C := ctxH C H4) wR fLitB [iLx] [vv wO] (litBlkBody C) [cellA C H3.length] (by decide) rfl
    (by decide) hcb ⟨by simp, trivial⟩ (litBlk_spec ra (ctxH C H4) (ctxOK_H hok _) s v H3.length hbo)
    (fun a s' H' hp => ?_)
  exact specR_returnI _ (Enc.idxW a) (by simp) (fun t ht =>
    ⟨H', hp2'.trans hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Str
