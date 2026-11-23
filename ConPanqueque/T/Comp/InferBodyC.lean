import ConPanqueque.T.Comp.InferProjC
import ConPanqueque.T.Core.InferForall
import ConPanqueque.T.Core.InferLamsLoop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `inferBody`

The full-grade inference body from its eight arms, given the knot's entries at fuel `n`.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `inferBody` runs besides the knot entries. -/
structure IbAll (C : Ctx) : Prop where
  ib : IbCodes C isBody (ikBody C) (ilBody C) (qfBody C) (qmBody C) (qaBody C) (pjBody C) ltBody
  lsucc : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  sort : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  ik : IkCodes C
  tq : TqCodes C
  qn : QnCodes C
  qa : QaCodes C
  pj : PjAll C
  ci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  cw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  cd : C.code.lookup fD = some (pmap dParams, dE C, .one)
  cI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  cI' : ExI.Codes C (ExI.body C)

section
variable {σ : Type}

theorem ib_body (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : IbAll C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (e : EIdx) (hd : d < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) ibBody s
      (ConRon.Arena.inferBody (knot mode C n) C.fe d e) (PostK C) :=
  ib_spec mode n C _ _ _ _ _ _ _ _ hc.ib s d e (by omega)
    (fun u => is_spec ra C hok hc.lsucc hc.sort s u)
    (fun c us _ => ik_pre ra hok hc.ik s c us)
    (fun l hv => il_spec ra C hok hc.ic s e l hv)
    (fun ty b => qf_spec ra mode n C hok hc.tq hE.hI hE.hW s d hd ty b)
    (fun ty b => qm_spec ra mode n C hok hc.qn hE.hI hE.hW s d hd ty b)
    (qa_spec ra mode n C hok hc.qa hE.hI hE.hW hE.hD hE.hDE s d hd e)
    (fun sn i pe hi => pj_pre ra mode n hok hc.pj hn hE s d hd sn i pe hi)
    (fun ty v b => lt_spec ra mode n C hok hc.ci hc.cw hc.cd hc.cI hc.cI' s d ty v b
      (fun H s1 hp e' => hE.hI H s1 d e' hp hd) (fun H s1 hp e' => hE.hW H s1 d e' hp hd)
      (fun H s1 hp a b => hE.hD H s1 d a b hp hd))

end

end ConPanqueque.T.Comp
