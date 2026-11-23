import ConPanqueque.T.Comp.IotaC
import ConPanqueque.T.Core.WhnfCore
import ConPanqueque.T.Core.WcStep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `whnfCoreBody`

The head normalization loop from its step (stuck-head ι, application β/ι, projection), given the knot's entries.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `whnfCoreBody` runs besides the knot entries. -/
structure WcAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  io : IoAll mode C
  cio : C.code.lookup fIota = some (ioParams.map (fun p => (p, ShapeHOL.one)), ioBody mode.verifiedChecks C, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  ms : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  mi : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
    ExK.mkaBody, .one)
  iapp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  gsp : C.code.lookup fGsp = some (gspParams.map (fun p => (p, ShapeHOL.one)), gspBody C, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  wc : C.code.lookup fWC = some (pmap wcParams, wcE, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  wap : C.code.lookup fWap = some (wapParams.map (fun p => (p, ShapeHOL.one)), wapBody C, .one)
  bp : C.code.lookup fBp = some (bpParams.map (fun p => (p, ShapeHOL.one)), bpBody, .one)
  wai : C.code.lookup fWai = some (waiParams.map (fun p => (p, ShapeHOL.one)), waiBody C, .one)
  q : ExQ.CodesQ C
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  rpc : RpcCodes C
  crpc : C.code.lookup fRPC = some (rpcParams.map (fun p => (p, ShapeHOL.one)), rpcBody mode.verifiedChecks C, .one)
  st : C.code.lookup fStuck = some (stParams.map (fun p => (p, ShapeHOL.one)), wstBody C, .one)
  sa : C.code.lookup fStepApp = some (apParams.map (fun p => (p, ShapeHOL.one)), wsaBody C, .one)
  sp : C.code.lookup fStepProj = some (prParams.map (fun p => (p, ShapeHOL.one)), wprBody, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)), ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  scf : C.code.lookup fSCF = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody .whnfCore C fSCF, .one)
  scc : C.code.lookup fSCC = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody .whnfCoreCheap C fSCC, .one)
  wcs : C.code.lookup fWCS = some (wcsParams.map (fun p => (p, ShapeHOL.one)), wcsBody, .one)
  wcl : C.code.lookup fWCL = some (wclParams.map (fun p => (p, ShapeHOL.one)), wclBody C, .one)

section
variable {σ : Type}

theorem wcs_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : WcAll mode C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (cheap : Bool) (d : Nat) (hd : d < 2 ^ 63) (h e : EIdx) :
    SpecR (σ := σ) (Pre C s (wcsParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW h,
      Enc.idxW e])) wcsBody s (whnfCoreStep mode (knot mode C n) C.fe cheap d h e) (PostWS C) := by
  refine wcs_spec ra mode n C hok _ _ _ hc.st hc.sa hc.sp hc.i1 hc.i1c s cheap d h e ?_ ?_ ?_
  · -- stuck head
    refine wst_spec ra mode n C hok _ hc.mg hc.mp hc.gaa hc.mka hc.iapp hc.cio s d h e ?_
    intro H s1 o sargs c us q cv mI rP isK rules hp hb hfc hci hle
    exact io_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc.io) hn (hE.at H C.St) s1 d hd c us cv mI rP isK rules q hci hfc
      sargs o hb hle
  · -- application
    refine wsa_spec mode n C hok hc.gsp hc.app hc.wc hc.af hc.gaa hc.wap s cheap d e
      (fun H s1 hp e' => hE.hWC H s1 cheap d e' hp hd) ?_
    intro H s1 v hd' va args nodes ov oa on same hp hbv hba hbn hnd hva has
    have hok' := ctxOK_H hok H
    have hw := wap_spec (σ := σ) ra mode n (ctxH C H) hok' hc.wap hc.bp hc.wai hc.app hc.mka hc.iapp d args nodes oa on
      hba hbn hnd has
      (fun H2 s2 t st hp2 hst i hi => bp_spec ra (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.q) hc.bp hc.irr hc.mka
        hc.iapp args oa (blkAt_mono hba hp2) (by omega) st hst (args.size - i) t i s2 rfl hi)
      (fun H2 s2 hd2 va2 ov2 hp2 hb2 hsz2 => wai_spec mode n (ctxH C H2) (ctxOK_H hok H2) _ hc.mg hc.mp hc.cio s2 d hd2
        va2 ov2 hb2 hsz2 (fun sargs c us q cv mI rP isK rules hb3 hfc hci hle =>
          io_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc.io) hn (hE.at H2 C.St) s2 d hd c us cv mI rP isK rules q hci
            hfc sargs ov2 hb3 hle))
      (args.size - 0) H s1 v hd' va ov same 0 (List.prefix_refl _) hbv hva rfl (Nat.zero_le _)
    exact hw
  · -- projection
    intro sn i pe hi
    exact wpr_spec mode n C _ hc.crpc hc.wc hc.w s cheap d e pe sn i (hE.hWC C.H s true d pe (List.prefix_refl _) hd)
      (hE.hW C.H s d pe (List.prefix_refl _) hd)
      (fun H s1 c hp => rpc_spec ra mode n (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.rpc) s1 d sn i c hi
        (fun H2 s2 hp2 e' => (hE.at H C.St).hW H2 s2 d e' hp2 hd))

theorem wcb_body (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : WcAll mode C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (cheap : Bool) (d : Nat) (hd : d < 2 ^ 63) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (wcParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e])) wcbBody s
      (whnfCoreBody mode (knot mode C n) C.fe cheap d e) (PostK C) :=
  wcb_spec mode n C hok wcsBody hc.scf hc.scc hc.ms hc.mi hc.mg hc.mp hc.af hc.wcs hc.wcl (fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun H s1 _ _ cheap' d' h e' hd' => wcs_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc) hn (hE.at H C.St) s1 cheap' d'
      hd' h e')
    s trivial cheap d hd e

end

end ConPanqueque.T.Comp
