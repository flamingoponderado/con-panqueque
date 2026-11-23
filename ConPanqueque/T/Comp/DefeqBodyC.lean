import ConPanqueque.T.Comp.DefeqStuckC
import ConPanqueque.T.Core.PropIrrel
import ConPanqueque.T.Core.DefeqBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `defeqBody`

The definitional-equality body from its arms (constructor targets, the lazy loop with proof irrelevance, lazy δ,
projection pairs and stuck terms), given the knot's entries.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code `defeqBody` runs besides the knot entries. -/
structure BqAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  bq : BqCodes C
  yz : YzCodes C C.side (priBody C) mode.verifiedChecks
  ldr : LdrAll mode C C.side
  dj : DjAll mode C
  dk : DkAll mode C
  pri : PriCodes C
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  hf : C.code.lookup ExM.fHasFvar = some ([(pFu, .one), (pH, .one)], ExM.hasFvarBody, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  na : C.code.lookup fNa = some (naParams.map (fun p => (p, ShapeHOL.one)), naBody, .one)
  cq : C.code.lookup fCq = some ([(cqE, .one)], cqBody C, .one)

section
variable {σ : Type}

theorem pri_pre (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (hok : CtxOK C) (hc : BqAll mode C)
    (hE : Ents (σ := σ) mode n C) (H : List (BitVec 64)) (s : AState) (d : Nat) (hd : d < 2 ^ 63) (a b : EIdx)
    (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (priParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (priBody C) s (propIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := fun t ht => by
  have h := sr_weakenH ht.1 hp
  exact pri_spec mode n C hok hc.pri s (sr_lwf h) ⟨h.cok.rn, h.cok.rl, h.cok.rls⟩ (sr_sortDen h) (sr_lpDen h)
    (sr_lpLen' h) (sr_lsDen h) (fun T tb hT => sr_tblSize h hT) d a b
    (fun H2 s2 hp2 e => hE.hIO H2 s2 d e hp2 hd) (fun H2 s2 hp2 e => hE.hW H2 s2 d e hp2 hd)
    (le_pre hok hc.dk.ls) H hp t ht

theorem bq_body (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : BqAll mode C) (hE : Ents (σ := σ) mode n C) (s : AState) (d : Nat) (hd : d < 2 ^ 63)
    (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (dParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (bqBody C) s (defeqBody mode C.side (knot mode C n) C.fe d a b) (PostB C) := by
  refine bq_spec mode n C hc.bq (fun _ => True) d (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ ?_ ?_ C.H s a b (List.prefix_refl _) trivial
  · intro H s1 _ _ o e
    exact cf_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.cF) hc.fvb hc.hf hc.af hc.mg hc.mp hc.na hc.cq C.side rfl s1 o e
  · intro H s1 hp _ e
    exact hE.hW H s1 d e hp hd
  · intro H s1 _ _ c w
    exact ch_spec (ctxH C H) (ctxOK_H hok H) hc.af hc.mg hc.mp s1 c w
  · intro H s1 hp _ a1 b1
    have hok' := ctxOK_H hok H
    have hE' := hE.at H C.St
    refine yz_spec mode n (ctxH C H) hok' C.side (priBody C) (by ctx_tr hc.yz) (fun _ => True) d
      (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ H s1 a1 b1
      (List.prefix_refl _) trivial
    · intro H2 s2 _ _ a2 b2
      exact qd_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc.ldr.ld) (hE.at H2 C.St) s2 d hd a2 b2
    · intro H2 s2 hp2 _ a2 b2
      exact pri_pre mode n hok hc hE H2 s2 d hd a2 b2 (hp.trans hp2)
    · intro H2 s2 hp2 _ c e
      exact hE'.hWC H2 s2 c d e hp2 hd
    · intro H2 s2 hp2 _ a2 b2
      exact ldr_pre ra mode n hok C.side rfl hc.ldr hE H2 s2 d hd a2 b2 (hp.trans hp2)
    · intro H2 s2 _ _ a2 b2
      exact dj_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc.dj) (hE.at H2 C.St) s2 d hd a2 b2
    · intro H2 s2 _ _ e
      exact hp_spec (ctxH C H2) hc.af s2 e
    · intro H2 s2 _ _ a2 b2
      exact dk_pre ra mode n (ctxOK_H hok H2) (by ctx_tr hc.dk) (hE.at H2 C.St) s2 d hd a2 b2
    · intro H2 s2 hp2 _ a2 b2
      exact hE'.hD H2 s2 d a2 b2 hp2 hd

end

end ConPanqueque.T.Comp
