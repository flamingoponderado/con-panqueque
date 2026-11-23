import ConPanqueque.T.Comp.RescueC
import ConPanqueque.T.Comp.WhnfBody
import ConPanqueque.T.Core.LazyDeltaStep
import ConPanqueque.T.Core.DeltaQuick
import ConPanqueque.T.Core.QuickDefEq
import ConPanqueque.T.Core.LazyDelta
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `quickDefEq` and one lazy-δ step
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `quickDefEq` and `lazyDeltaStep` run besides the knot entries. -/
structure LdAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ld : LdCodes C
  qd : QdCodes C mode.verifiedChecks
  ds : DsCodes C
  ls : LsCodes C
  uf : UfCodes C
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  hp : C.code.lookup fHp = some ([(hpE, .one)], hpBody, .one)
  wc : C.code.lookup fWC = some (pmap wcParams, wcE, .one)
  cqd : C.code.lookup fQd = some (qdParams.map (fun p => (p, ShapeHOL.one)), qdBody C, .one)

section
variable {σ : Type}

theorem qd_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : LdAll mode C) (hE : Ents (σ := σ) mode n C) (s : AState) (d : Nat) (hd : d < 2 ^ 63)
    (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (qdParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (qdBody C) s
      (quickDefEq mode (knot mode C n) d a b) (PostOBH C) :=
  qd_spec ra mode n C hok hc.qd hE.hI hE.hD (le_pre hok hc.ls) s d (by omega) a b

theorem lds_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : LdAll mode C) (hE : Ents (σ := σ) mode n C) (s : AState) (d : Nat) (hd : d < 2 ^ 63)
    (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (ldParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) ldBody s
      (lazyDeltaStep mode (knot mode C n) C.fe d a b) (PostDS C) :=
  lds_spec mode n C hc.ld (fun _ => True) d hd (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun H s1 _ _ e => uk_spec (ctxH C H) (ctxOK_H hok H) hc.af hc.mg hc.mp s1 e)
    (fun H s1 _ _ e => hn_spec (ctxH C H) (ctxOK_H hok H) hc.af hc.mg hc.mp s1 e)
    (fun H s1 _ _ a b => sq_spec (ctxH C H) hc.af s1 a b)
    (fun H s1 _ _ d' e hd' => tu_spec mode n (ctxH C H) hc.af hc.hp hc.wc
      (fun H2 s2 c d2 e2 hp2 hd2 => (hE.at H C.St).hWC H2 s2 c d2 e2 hp2 hd2) s1 d' hd' e)
    (fun H s1 _ _ e => uf_pre ra (ctxOK_H hok H) (ufCodes_H hc.uf H) s1 e)
    (fun H s1 _ _ c d' e hd' => hE.wc H C.St s1 c d' e hd')
    (fun H s1 _ _ d' a b hd' => ds_spec mode n (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.ds) d'
      (fun H2 s2 hp2 a2 b2 => (hE.at H C.St).hD H2 s2 d' a2 b2 hp2 hd')
      (fun H2 s2 u v _ => specR_mono (LLeq.lvlsEqQ_spec' (ctxH C H) (ctxOK_H hok H) hc.ls.S hc.ls.N hc.ls.M hc.ls.Cb
        hc.ls.B hc.ls.I hc.ls.R hc.ls.E hc.ls.Tr hc.ls.L hc.ls.V hc.ls.G H2 u v s2) (fun _ h => h)
        (fun _ _ _ _ ⟨_, _, h⟩ => h)) s1 a b)
    (fun H s1 _ _ a b => dq_spec mode n (ctxH C H) (ctxOK_H hok H) hc.cqd
      (fun H2 s2 a2 b2 _ => qd_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc) (hE.at H2 C.St) s2 d hd a2 b2) s1 a b)
    s trivial a b


/-- The code lazy-δ reduction runs besides the knot entries. -/
structure LdrAll (mode : ConLeche.CheckMode) (C : Ctx) (v : Bool) : Prop where
  ldr : LdrCodes C v
  ld : LdAll mode C
  wb : WbCodes C
  iz : C.code.lookup fIz = some ([izE].map (fun p => (p, ShapeHOL.one)), izBody C, .one)
  np : C.code.lookup fNp = some ([npE].map (fun p => (p, ShapeHOL.one)), npBody C, .one)
  nl : NlCodes C
  cd : C.code.lookup fD = some (pmap dParams, dE C, .one)
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  hf : C.code.lookup ExM.fHasFvar = some ([(pFu, .one), (pH, .one)], ExM.hasFvarBody, .one)

theorem ldr_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (v : Bool) (hv : C.side = v) (hc : LdrAll mode C v) (hE : Ents (σ := σ) mode n C)
    (H : List (BitVec 64)) (s : AState) (d : Nat) (hd : d < 2 ^ 63) (a b : EIdx) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ldrParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      BitVec.ofNat 64 defeqLoopFuel, Enc.idxW a, Enc.idxW b])) (ldrBody v C) s
      (lazyDeltaReduction mode v (knot mode C n) C.fe d defeqLoopFuel a b) (PostLR (ctxH C H)) :=
  ldr_spec mode n C hok v hv hc.ldr (fun _ => True) d (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (fun H1 s1 _ _ a1 b1 => of_spec ra mode n (ctxH C H1) (ctxOK_H hok H1) hc.iz hc.np (by ctx_tr hc.nl) hc.cd
      (hE.at H1 C.St).hD s1 d hd a1 b1)
    (fun H1 s1 _ _ a1 b1 => dn_spec (ctxH C H1) (ctxOK_H hok H1) (by ctx_tr hc.cF) hc.fvb hc.hf s1 a1 b1)
    (fun H1 s1 _ _ e => rd_spec ra mode n (ctxH C H1) (ctxOK_H hok H1) (bigCodes_H hc.wb.big H1) (rdCodes_H hc.wb.rd H1)
      (fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun H2 s2 hp2 _ d' e' hd' => (hE.at H1 C.St).hW H2 s2 d' e' hp2 hd')
      s1 trivial d hd e)
    (fun H1 s1 _ _ a1 b1 => hE.d H1 C.St s1 d a1 b1 hd)
    (fun H1 s1 _ _ a1 b1 => lds_pre ra mode n (ctxOK_H hok H1) (by ctx_tr hc.ld) (hE.at H1 C.St) s1 d hd a1 b1)
    defeqLoopFuel (by unfold defeqLoopFuel; omega) H s a b hp trivial

end

end ConPanqueque.T.Comp
