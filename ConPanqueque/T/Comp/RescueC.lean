import ConPanqueque.T.Core.RescueAnd
import ConPanqueque.T.Comp.IotaFamC
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: `prepareMajor` and the major-premise rescues

The K-like, structure-η and `And` rescues, the rescue dispatcher, and `prepareMajor`, given the knot's entries.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The code the rescues and `prepareMajor` run besides the knot entries. -/
structure PmAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  pm : PmCodes C (rsBody C)
  rs : RsCodes C (rkBody mode.verifiedChecks) reBody (raBody mode.verifiedChecks C)
  rk : RkCodes C fsoBody
  re : ReCodes C fsoBody fzBody
  ra : RaCodes C fsoBody
  fso : FsoCodes C
  fz : FzCodes C
  ls : LsCodes C

section
variable {σ : Type}

/-- `lvlEq?` on two valid levels. -/
theorem le_pre {C : Ctx} (hok : CtxOK C) (hc : LsCodes C) :
    ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1
        (lvlEq? u v) (LLeq.PostOB (ctxH C H)) := by
  intro H s1 u v _ hu hv t ht
  obtain ⟨lu, hlu⟩ := Option.isSome_iff_exists.mp hu
  obtain ⟨lv, hlv⟩ := Option.isSome_iff_exists.mp hv
  exact specR_mono (LLeq.lvlEqQ_spec C hok hc.S hc.N hc.M hc.Cb hc.B hc.I hc.R hc.E hc.Tr hc.L H u v s1 lu lv hlu hlv
    ht.1.cok.rl ht.1.cok.le) (fun _ h => h) (fun _ _ _ _ ⟨_, _, h⟩ => h) t ht

theorem rs_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : PmAll mode C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (c : NIdx) (isK : Bool) (rules : List IRecRule) (rw : BitVec 64)
    (m : EIdx) (hrules : RulesE C.EB C.EH rw rules) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
      Enc.idxW m])) (rsBody C) s (majorToCtorRescue mode (knot mode C n) C.fe d c isK rules m) (PostK C) := by
  refine rs_spec mode n C hok _ _ _ hc.rs s d c isK rules rw m hrules ?_ ?_ ?_
  · intro H s1 rl qr cvj cnP nF T qj hp hrule hcij
    have hE' := hE.at H C.St
    exact rk_spec ra mode n (ctxH C H) (ctxOK_H hok H) _ (by ctx_tr hc.rk) s1 d rl qr cvj cnP nF T qj m hrule hcij
      (fun H2 s2 hp2 e => hE'.hIO H2 s2 d e hp2 hd) (fun H2 s2 hp2 e => hE'.hW H2 s2 d e hp2 hd)
      (fun H2 s2 hp2 a b => hE'.hD H2 s2 d a b hp2 hd)
      (fso_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.fso) d (by omega))
      (le_pre (ctxOK_H hok H) (by ctx_tr hc.ls))
  · intro H s1 rl qr cvj cnP nF T qj cvT caps qT tbl o hp hrule hcij hcT hfT htb
    have hE' := hE.at H C.St
    refine re_spec ra mode n (ctxH C H) (ctxOK_H hok H) _ _ (by ctx_tr hc.re) s1 d rl qr cvj cnP nF T qj m cvT caps
      qT tbl o hcT htb (fun H2 s2 hp2 e => hE'.hIO H2 s2 d e hp2 hd) (fun H2 s2 hp2 e => hE'.hW H2 s2 d e hp2 hd)
      (fso_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.fso) d (by omega)) ?_
    intro H2 s2 us hp2 t ht
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h T _ hfT
    have hlen := sr_lpLen h T _ hfT
    have hden := sr_tyDen h T _ hfT
    simp only [IConstantInfo.toConstantVal] at hks hlen hden
    exact fz_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) (by ctx_tr hc.fz) hn
      (fun H3 s3 hp3 d' e' hd' => (hE.at H2 C.St).hW H3 s3 d' e' hp3 hd') s2 d cvT caps qT hcT us (sr_lwf h)
      (sr_stateOK h) ks hks h.cok.rn h.cok.rl h.cok.rls hden hlen (sr_capsLen h hfT) t ht
  · intro H s1 rl qr cvj cnP nF T qj hp hrule hcij
    have hE' := hE.at H C.St
    exact ra_spec ra mode n (ctxH C H) (ctxOK_H hok H) _ (by ctx_tr hc.ra) s1 d rl qr cvj cnP nF T qj m hrule hcij
      (fun H2 s2 hp2 e => hE'.hIO H2 s2 d e hp2 hd) (fun H2 s2 hp2 e => hE'.hW H2 s2 d e hp2 hd)
      (fun H2 s2 hp2 a b => hE'.hD H2 s2 d a b hp2 hd)
      (fso_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.fso) d (by omega))
      (le_pre (ctxOK_H hok H) (by ctx_tr hc.ls))

theorem pm_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : PmAll mode C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (c : NIdx) (isK : Bool) (rules : List IRecRule) (rw : BitVec 64)
    (m : EIdx) (hrules : RulesE C.EB C.EH rw rules) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
      Enc.idxW m])) pmBody s (prepareMajor mode (knot mode C n) C.fe d c isK rules m) (PostMV C) :=
  pm_spec ra mode n C hok _ hc.pm s d c isK rules rw m (fun H s1 hp e => hE.hW H s1 d e hp hd)
    (fun m' H s1 _ => rs_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc) hn (hE.at H C.St) s1 d hd c isK rules rw m'
      hrules)

end

end ConPanqueque.T.Comp
