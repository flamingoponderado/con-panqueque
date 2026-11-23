import ConPanqueque.T.Comp.DefeqProjC
import ConPanqueque.T.Core.DefeqStuck
import ConPanqueque.T.Core.StructUnitCert
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: stuck terms (`defeqStuck`)

η certificates, structure η/unit certificates and proof irrelevance at stuck heads, given the knot's entries.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `defeqStuck` runs besides the knot entries. -/
structure DkAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  dk : DkCodes C mode.verifiedChecks
  dk2 : DkCodes2 C
  ls : LsCodes C
  tc : Str.TcCodes C
  si : SiCodes C sucBody
  set : SetCodes C
  sw : SwCodes C
  es : EsCodes C
  suc : SucCodes C
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  e : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  nu : C.code.lookup fNu = some ([(nuE, .one)], nuBody, .one)
  cd : C.code.lookup fD = some (pmap dParams, dE C, .one)
  ci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)), ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  ap : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)

section
variable {σ : Type}

theorem lsq_pre {C : Ctx} (hok : CtxOK C) (hc : LsCodes C) :
    ∀ (H : List (BitVec 64)) s1 (u v : LsIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (LLeq.lsParams.zip [Enc.idxW u, Enc.idxW v, BitVec.ofNat 64 0])) LLeq.lsGoBody
        s1 (lvlsEq? u v) (LLeq.PostOB (ctxH C H)) :=
  fun H s1 u v _ => specR_mono (LLeq.lvlsEqQ_spec' C hok hc.S hc.N hc.M hc.Cb hc.B hc.I hc.R hc.E hc.Tr hc.L hc.V hc.G
    H u v s1) (fun _ h => h) (fun _ _ _ _ ⟨_, _, h⟩ => h)

theorem si_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : DkAll mode C) (hE : Ents (σ := σ) mode n C) :
    ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (siParams.zip
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) siBody s1
      (stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H s1 d a b hp hd
  have hok' := ctxOK_H hok H
  have hE' := hE.at H C.St
  refine si_spec mode n (ctxH C H) sucBody (by ctx_tr hc.si) ?_ ?_ ?_ H s1 d a b (List.prefix_refl _) hd
  · intro H2 s2 d2 a2 b2 hp2 hd2
    refine cc_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.set) (hE.at H2 C.St).hIO (hE.at H2 C.St).hW
      (hE.at H2 C.St).hD ?_ ?_ ?_ H2 s2 d2 hd2 a2 b2 (List.prefix_refl _)
    · intro H3 s3 d3 a3 b3 w hp3 hd3
      exact sw_spec ra mode n (ctxH C H3) (ctxOK_H hok H3) (by ctx_tr hc.sw) d3
        (fun H4 s4 hp4 a4 b4 => (hE.at H3 C.St).hD H4 s4 d3 a4 b4 hp4 hd3)
        (lsq_pre (ctxOK_H hok H3) (by ctx_tr hc.ls)) s3 a3 b3 w
    · intro H3 s3 a3 _
      exact es_spec (ctxH C H3) (ctxOK_H hok H3) (by ctx_tr hc.es) s3 a3
    · intro H3 s3 a3 _
      exact ep_spec (ctxH C H3) (ctxOK_H hok H3) (by ctx_tr hc.es) s3 a3
  · intro H2 s2 d2 a2 b2 hp2 hd2 t ht
    exact suc_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.suc) (fun _ => True)
      (fun c ci hf => sr_lpLen ht.1 c ci hf) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
      (hE.at H2 C.St).hIO (hE.at H2 C.St).hW (le_pre (ctxOK_H hok H2) (by ctx_tr hc.ls))
      (fun _ _ _ _ _ _ _ => trivial) (hE.at H2 C.St).hD H2 s2 d2 a2 b2 (List.prefix_refl _) trivial hd2 t ht
  · intro H2 s2 d2 a2 b2 hp2 hd2
    exact pi_spec mode n (ctxH C H2) (ctxOK_H hok H2) hc.io hc.w hc.e s2 d2 a2 b2
      (fun H3 s3 hp3 e => (hE.at H2 C.St).hIO H3 s3 d2 e hp3 hd2) (fun H3 s3 hp3 e => (hE.at H2 C.St).hW H3 s3 d2 e hp3 hd2)
      (le_pre (ctxOK_H hok H2) (by ctx_tr hc.ls))

theorem dk_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : DkAll mode C) (hE : Ents (σ := σ) mode n C) (s : AState) (d : Nat) (hd : d < 2 ^ 63)
    (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (dkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (dkBody C) s
      (defeqStuck mode (knot mode C n) C.fe d a b) (PostB C) :=
  dk_spec mode n C hok hc.dk (si_pre ra mode n hok hc hE)
    (fun H s1 d' ty bd e hp hd' => ec_spec ra mode n (ctxH C H) (ctxOK_H hok H) _ rfl hc.af hc.nu hc.io hc.w hc.cd hc.ci
      hc.i1 (by ctx_tr hc.i1c) hc.fv hc.ap (hE.at H C.St).hIO (hE.at H C.St).hW (hE.at H C.St).hI (hE.at H C.St).hD
      s1 d' hd' ty bd e)
    hc.dk2 hE.hD (lsq_pre hok hc.ls)
    (fun H s1 h str _ hv => Str.tc_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.tc) s1 h str hv)
    s d hd a b

end

end ConPanqueque.T.Comp
