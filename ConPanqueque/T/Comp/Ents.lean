import ConPanqueque.T.Knot
import ConPanqueque.T.Floor
import ConPanqueque.T.CtxTr
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The knot's entries at every derived context

`Ents mode n C`: the six entry points at fuel `n`, as callees, at every context `ctxSt (ctxH C H) St` (any heap
image, any store floor). The family is closed under `ctxH` and `ctxSt` up to definitional equality, so an arm
spec instantiated at a derived context finds its entry hypotheses here too.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T.Knot

section
variable {σ : Type}

structure Ents (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) : Prop where
  wc : ∀ (H : List (BitVec 64)) (St : EStore) s c d e, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) wcParams
    [BitVec.ofNat 64 n, boolW c, BitVec.ofNat 64 d, Enc.idxW e] wcE s ((knot mode C n).whnfCore c d e)
    (PostK (ctxSt (ctxH C H) St))
  w : ∀ (H : List (BitVec 64)) (St : EStore) s d e, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) kParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s ((knot mode C n).whnf d e)
    (PostK (ctxSt (ctxH C H) St))
  i : ∀ (H : List (BitVec 64)) (St : EStore) s d e, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) kParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (inferE C fIB) s ((knot mode C n).infer d e)
    (PostK (ctxSt (ctxH C H) St))
  d : ∀ (H : List (BitVec 64)) (St : EStore) s d a b, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) dParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s ((knot mode C n).defeq d a b)
    (PostB (ctxSt (ctxH C H) St))
  de : ∀ (H : List (BitVec 64)) (St : EStore) s d a b, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) dParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dEE C) s ((knot mode C n).defeqE d a b)
    (PostB (ctxSt (ctxH C H) St))
  io : ∀ (H : List (BitVec 64)) (St : EStore) s d e, d < 2 ^ 63 → Callee (σ := σ) (ctxSt (ctxH C H) St) kParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (inferIOE C fIOB) s ((knot mode C n).inferIO d e)
    (PostK (ctxSt (ctxH C H) St))

/-- The entries at a derived context. -/
theorem Ents.at {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C)
    (H : List (BitVec 64)) (St : EStore) : Ents (σ := σ) mode n (ctxSt (ctxH C H) St) :=
  ⟨fun H' St' => h.wc H' St', fun H' St' => h.w H' St', fun H' St' => h.i H' St', fun H' St' => h.d H' St',
    fun H' St' => h.de H' St', fun H' St' => h.io H' St'⟩

/-- The entry families in the shape the arm specs take (at `ctxH C H`). -/
theorem Ents.hW {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d e, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s1 ((knot mode C n).whnf d e)
      (PostK (ctxH C H)) := fun H s1 d e _ hd => h.w H C.St s1 d e hd

theorem Ents.hI {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d e, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (inferE C fIB) s1 ((knot mode C n).infer d e)
      (PostK (ctxH C H)) := fun H s1 d e _ hd => h.i H C.St s1 d e hd

theorem Ents.hIO {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d e, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e)
      (PostK (ctxH C H)) := fun H s1 d e _ hd => h.io H C.St s1 d e hd

theorem Ents.hD {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)) := fun H s1 d a b _ hd => h.d H C.St s1 d a b hd

theorem Ents.hDE {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dEE C) s1 ((knot mode C n).defeqE d a b)
      (PostB (ctxH C H)) := fun H s1 d a b _ hd => h.de H C.St s1 d a b hd

theorem Ents.hWC {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx} (h : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 c d e, C.H <+: H → d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW c, BitVec.ofNat 64 d, Enc.idxW e] wcE s1 ((knot mode C n).whnfCore c d e)
      (PostK (ctxH C H)) := fun H s1 c d e _ hd => h.wc H C.St s1 c d e hd

end

end ConPanqueque.T.Comp
