import ConPanqueque.T.Comp.RescueC
import ConPanqueque.T.Core.RuleBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Composition: ι reduction at a recursor

`iotaRecAt` from `prepareMajor`, the family certificate and the rule body, given the knot's entries.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.T.ILP (fInstLPF ilpfBody CodesILP ilpBody ilpParams)

/-- The code `iotaRecAt` runs besides the knot entries. -/
structure IoAll (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  io : IoCodes C pmBody (fmBody C) (rbBody C)
  pm : PmAll mode C
  fm : FmAll C
  ilp : CodesILP C (ilpBody C)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  lb : C.code.lookup fLb = some (lbParams.map (fun p => (p, ShapeHOL.one)), lbBody, .one)

section
variable {σ : Type}

theorem io_pre (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : IoAll mode C) (hn : n < 2 ^ 64) (hE : Ents (σ := σ) mode n C)
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (c : NIdx) (us : LsIdx) (cv : IConstantVal) (mI rP : Nat) (isK : Bool)
    (rules : List IRecRule) (q : Nat) (hci : CIE C.EB C.EH q (.recInfo cv mI rP isK rules))
    (hfc : C.fe.find? c = some (.recInfo cv mI rP isK rules))
    (sargs : List EIdx) (oa : Nat) (hba : BlkAt C.H oa (sargs.map Enc.idxW)) (hle : mI + 1 ≤ sargs.length) :
    SpecR (σ := σ) (Pre C s (ioParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us, ecell C q,
      cellA C oa, BitVec.ofNat 64 (mI + 1)])) (ioBody mode.verifiedChecks C) s
      (iotaRecAt mode (knot mode C n) C.fe d c us cv mI rP isK rules (takeEidx sargs.toArray (mI + 1)))
      (UD.PostO C) := by
  refine io_spec ra mode n C hok _ _ _ hc.io s d c us cv mI rP isK rules q hci hfc sargs oa hba hle ?_ ?_ ?_
  · intro H s1 m rw hp hrules
    exact pm_pre ra mode n (ctxOK_H hok H) (by ctx_tr hc.pm) hn (hE.at H C.St) s1 d hd c isK rules rw m hrules
  · intro hv H s1 usj qj cvj cnP nF ind qr rl om margs hp hcij hrule ⟨cj, hfj⟩ hrl hbm t ht
    have hsl := blk_small0 hok (sr_weakenH ht.1 hp) hba
    have hml := blk_small0 (ctxOK_H hok H) ht.1 hbm
    simp only [List.length_map] at hsl hml
    exact fm_pre ra mode hv n hok hc.fm hn hE d hd s1 c us cv mI rP isK rules q hci hfc sargs oa hba hle hsl usj qj cvj
      cnP nF ind hcij hfj qr rl hrule hrl om margs hml H hp hbm t ht
  · intro H s1 wl rl k hp ⟨o, hwo, hblk⟩ _ hk t ht
    have h := ht.1
    obtain ⟨ks, hks⟩ := sr_lpDen h c _ hfc
    have hlen := sr_lpLen h c _ hfc
    simp only [IConstantInfo.toConstantVal] at hks hlen
    subst hwo
    exact rb_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.ilp) hc.ilpf hc.lb s1 c rl.ctor cv.levelParams ks rl.rhs
      k us o hblk hlen hk hks (sr_stateOK h) h.cok.rn h.cok.rl h.cok.rls t ht

end

end ConPanqueque.T.Comp
