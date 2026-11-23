import ConPanqueque.T.Core.Whnf
import ConPanqueque.T.Core.Unfold
import ConPanqueque.T.SRFacts
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Composition: `whnfBody`

`whnfBody`'s loop calls `whnfCore`, `reduceNat` and `unfoldDefinition`. The first is a knot entry; the other
two are discharged here from their specs, with their state facts read off the state relation.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.T.ILP (fInstLPF ilpfBody CodesILP ilpBody)
open ConPanqueque.T.CV (cvBody cvParams)

/-- The code `unfoldDefinition` runs. -/
structure UfCodes (C : Ctx) : Prop where
  uf : C.code.lookup UD.fUnfold = some (pmap [UD.uE], UD.ufBody C, .one)
  ilp : CodesILP C (ilpBody C)
  ilpf : C.code.lookup fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  cv : C.code.lookup fCV = some (cvParams.map (fun p => (p, ShapeHOL.one)), cvBody C, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
    ExK.mkaBody, .one)
  ud : C.code.lookup UD.fUD = some (UD.udParams.map (fun p => (p, ShapeHOL.one)), UD.udBody, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)

theorem ufCodes_H {C : Ctx} (hc : UfCodes C) (H : List (BitVec 64)) : UfCodes (ctxH C H) :=
  ⟨hc.uf, ⟨hc.ilp.1, hc.ilp.2, hc.ilp.3, hc.ilp.4, hc.ilp.5, hc.ilp.6, hc.ilp.7, hc.ilp.8, hc.ilp.9, hc.ilp.10, hc.ilp.11, hc.ilp.12, hc.ilp.13, hc.ilp.14, hc.ilp.15, hc.ilp.16, hc.ilp.17, hc.ilp.18, hc.ilp.19, hc.ilp.20, hc.ilp.21, hc.ilp.22, hc.ilp.23, hc.ilp.24, hc.ilp.25, hc.ilp.26⟩,
    hc.ilpf, hc.cv, hc.gaa, hc.mka, hc.ud, hc.af⟩

/-- The code `whnfBody` runs besides the knot entries. -/
structure WbCodes (C : Ctx) : Prop where
  rn : C.code.lookup fRN = some (pmap kParams, rdBody C, .one)
  big : BigCodes C
  rd : RdCodes C
  uf : UfCodes C

theorem rdCodes_H {C : Ctx} (hc : RdCodes C) (H : List (BitVec 64)) : RdCodes (ctxH C H) :=
  ⟨hc.raw, hc.w, fun e he => by
    have h := hc.nb e he
    simp only [rdTab, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact h⟩

theorem wbCodes_H {C : Ctx} (hc : WbCodes C) (H : List (BitVec 64)) : WbCodes (ctxH C H) :=
  ⟨hc.rn, bigCodes_H hc.big H, rdCodes_H hc.rd H, ufCodes_H hc.uf H⟩

section
variable {σ : Type}

/-- `unfoldDefinition` from the state relation alone. -/
theorem uf_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hc : UfCodes C)
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s ([UD.uE].zip [Enc.idxW e])) (UD.ufBody C) s (unfoldDefinition C.fe e) (UD.PostO C) :=
  fun t ht => have h := ht.1
    UD.uf_spec ra C hok hc.ilp hc.ilpf hc.cv hc.gaa hc.mka hc.ud hc.af s e (sr_stateOK h) h.cok.rn h.cok.rl
      h.cok.rls (fun hh n us cv value hint _ hv hf => sr_ufPre h hh n us cv value hint hv hf) t ht

/-- `whnfBody`, given the knot's `whnfCore` and `whnf` entries at every extension of the heap. -/
theorem wb_body (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hcwc : C.code.lookup fWC = some (pmap wcParams, wcE, .one)) (hc : WbCodes C)
    (hWC : ∀ (H : List (BitVec 64)) s1 d e, Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW e] wcE s1
      ((knot mode C n).whnfCore false d e) (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d e, Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s1 ((knot mode C n).whnf d e)
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) WB.wbBody s
      (whnfBody (knot mode C n) C.fe d e) (PostK C) :=
  WB.wb_spec mode n C hok hcwc hc.rn hc.uf.uf (fun _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (fun H s1 _ _ => hWC H s1)
    (fun H s1 _ _ d e => rd_spec ra mode n (ctxH C H) (ctxOK_H hok H) (bigCodes_H hc.big H) (rdCodes_H hc.rd H)
      (fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun H' s2 _ _ => hW H' s2) s1 trivial d e)
    (fun H s1 _ _ e => uf_pre ra (ctxOK_H hok H) (ufCodes_H hc.uf H) s1 e) s trivial d e

end

end ConPanqueque.T.Comp
