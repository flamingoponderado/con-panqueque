import ConPanqueque.T.Core.InferArms
import ConPanqueque.T.Core.InferLit
import ConPanqueque.T.Core.ConstTy
import ConPanqueque.T.SRFacts
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `inferBody`'s leaf arms

The sort, constant and literal arms, with their state facts read off the state relation.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.T.ILP (fInstLPF ilpfBody CodesILP ilpBody)

section
variable {σ : Type}

theorem sr_lsChild {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {e : EIdx} {v : ENodeView}
    (hv : s.store.view e = some v) {us : LsIdx} (hu : us ∈ v.lschildren) :
    ∃ vs, denoteLs s.store.lss us = some vs := by
  obtain ⟨rk, w⟩ := h.twf
  exact Option.isSome_iff_exists.mp (denoteLs_total' (sr_lswf h) (w.lschildOK e _ hv us hu).1)

/-- The code the constant arm runs. -/
structure IkCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  ct : C.code.lookup CT.fCT = some (CV.cvParams.map (fun p => (p, ShapeHOL.one)), CT.ctBody C, .one)
  ilp : CodesILP C (ilpBody C)
  ilpf : C.code.lookup fInstLPF = some (ILP.ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)

theorem ik_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hc : IkCodes C)
    (s : AState) (c : NIdx) (us : LsIdx) :
    SpecR (σ := σ) (Pre C s (ibcParams.zip [Enc.idxW c, Enc.idxW us])) (ikBody C) s (ibConstT C.fe c us)
      (PostK C) := fun t ht => by
  have h := ht.1
  refine WC.ik_spec C hok hc.mg hc.mp hc.ct s c us (fun ci o ok hf _ hblk => ?_) t ht
  obtain ⟨ks, hks⟩ := sr_lpDen h c ci hf
  exact CT.ct_spec ra C hok hc.ilp hc.ilpf s ci.toConstantVal ks us ok hblk (sr_lpLen h c ci hf) hks
    (sr_stateOK h) h.cok.rn h.cok.rl h.cok.rls (sr_tyDen h c ci hf)

end

end ConPanqueque.T.Comp
