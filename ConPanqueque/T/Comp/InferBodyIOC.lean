import ConPanqueque.T.Comp.InferBodyC
import ConPanqueque.T.Core.InferBodyIO
import ConPanqueque.T.Core.IoView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `inferBodyIO`

The io-grade inference body from its eight arms, given the knot's entries at fuel `n`.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `inferBodyIO` runs besides the knot entries. -/
structure IbioAll (C : Ctx) : Prop where
  ibio : IbioCodes C isBody (ikBody C) (ilBody C) qfoBody qmoBody (qaoBody C) (pjioBody C) ltoBody
  lsucc : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  sort : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  ik : IkCodes C
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  cw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  cI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  cI' : ExI.Codes C (ExI.body C)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  im : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  cA : C.code.lookup ExA.fAbs1F = some ([pFu, ExA.pAd, ExI.pD, pH].map (fun p => (p, ShapeHOL.one)),
    ExA.fastBodyA C, .one)
  cA' : ExA.CodesA C (ExA.bodyA C)
  qao : QaoCodes C
  pjio : PjioCodes C
  pj : PjAll C

section
variable {σ : Type}

theorem pjio_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hio : PjioCodes C) (hc : PjAll C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (sn : NIdx) (i : Nat) (pe : EIdx) (hi : i < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i,
      Enc.idxW pe])) (pjioBody C) s (inferProj (CoreFnsA.ioView (knot mode C n)) C.fe d sn i pe) (PostK C) :=
  pjio_spec mode n C hok hio (fun _ => True) hE.hIO hE.hW (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun H s1 tbl ot i us _ _ htb _ hi =>
      gd_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc.gd) (by ctx_tr hc.fz) (by ctx_tr hc.zw) (by ctx_tr hc.gw)
        (by ctx_tr hc.ik) (by ctx_tr hc.cg) hn (hE.at H C.St) tbl ot htb i hi us s1)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun H s1 tbl ot i us targs oa pe hp _ htb hT hba hi => ta_pre ra hok hc.ta H s1 tbl ot i us targs oa pe hp htb hT hba hi)
    s trivial d hd sn i pe hi

theorem ibio_body (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : IbioAll C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (e : EIdx) (hd : d < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) ibioBody s
      (ConRon.Arena.inferBodyIO (CoreFnsA.ioView (knot mode C n)) C.fe d e) (PostK C) :=
  ibio_spec mode n C _ _ _ _ _ _ _ _ hc.ibio s d e (by omega)
    (fun u => is_spec ra C hok hc.lsucc hc.sort s u)
    (fun c us _ => ikIO_spec C hok hc.ik.mg hc.ik.mp hc.ik.ct s c us
      (fun ci _ ok hf _ hblk => ct_pre ra hok hc.ik s hf ok hblk us))
    (fun l hv => il_spec ra C hok hc.ic s e l hv)
    (fun ty b => qfo_spec ra mode n C hok hc.io hc.cw hc.cI hc.cI' hc.fv hc.im hc.sort hE.hIO hE.hW s d hd ty b)
    (fun ty b => qmo_spec ra mode n C hok hc.io hc.cI hc.cI' hc.fv hc.cA hc.cA' hE.hIO s d hd ty b)
    (qao_spec ra mode n C hok hc.qao hE.hIO hE.hW s d hd e)
    (fun sn i pe hi => pjio_pre ra mode n hok hc.pjio hc.pj hn hE s d hd sn i pe hi)
    (fun ty v b => lto_spec ra mode n C hok hc.io hc.cI hc.cI' hE.hIO s d hd ty v b)

end

end ConPanqueque.T.Comp
