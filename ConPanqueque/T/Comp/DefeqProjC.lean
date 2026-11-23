import ConPanqueque.T.Comp.LazyDeltaC
import ConPanqueque.T.Comp.WhnfCoreC
import ConPanqueque.T.Core.DefeqProj
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: projection pairs (`defeqProjPair`)
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `defeqProjPair` runs besides the knot entries. -/
structure DjAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  lpr : LprCodes C mode.verifiedChecks
  clpr : C.code.lookup fLpr = some (lprParams.map (fun p => (p, ShapeHOL.one)), lprBody mode.verifiedChecks C, .one)
  ld : LdAll mode C
  rpc : RpcCodes C

section
variable {σ : Type}

theorem dj_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : DjAll mode C) (hE : Ents (σ := σ) mode n C) (s : AState) (d : Nat) (hd : d < 2 ^ 63)
    (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (djParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (djBody mode.verifiedChecks C) s (defeqProjPair mode (knot mode C n) C.fe d a b) (PostB C) :=
  dj_spec mode n C hc.clpr (fun _ => True) d
    (fun H s1 hp _ sn i a1 b1 hi => lpr_spec mode n (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.lpr) (fun _ => True) d sn i
      (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      (fun H2 s2 _ _ a2 b2 => lds_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc.ld) (hE.at H2 C.St) s2 d hd a2 b2)
      (fun H2 s2 _ _ e => rpc_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.rpc) s2 d sn i e hi
        (fun H3 s3 hp3 e3 => (hE.at H2 C.St).hW H3 s3 d e3 hp3 hd))
      (fun H2 s2 _ _ a2 b2 => hE.d H2 C.St s2 d a2 b2 hd)
      defeqLoopFuel (by unfold defeqLoopFuel; omega) H s1 a1 b1 (List.prefix_refl _) trivial)
    s trivial a b

end

end ConPanqueque.T.Comp
