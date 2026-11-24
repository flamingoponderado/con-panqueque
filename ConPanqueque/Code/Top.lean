import ConPanqueque.Code.Fold
import ConPanqueque.Code.Front

/-! # The top verdict at the concrete code table

`top_verdict` with its code-table assumptions (`FrontCodes`, `FoldCodes`, the `feed` entry)
discharged by the concrete table `codeEntries` (`fold_ok`, `front_ok`, `feed_ok`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Front
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Code

theorem top_verdict_table {σ : Type} (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hC : C.code = codeMap (codeEntries C))
    (hok : CtxOK C) (hf : FrontOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : PersPins s) (hpins : PinsDenote s.store pins pinsP)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1, kBN, kBA], x ∈ D)
    (rb capD jN cap j0 Lw : Nat)
    (hlay : jN + 3 * cap ≤ rb) (hbuf0 : rb + 1 + capD ≤ j0 + 1) (hcells : j0 + Lw ≤ C.H.length)
    (hL16 : 16 ≤ 8 * Lw) (h59 : 8 * Lw < 2 ^ 59)
    (hal : (cellA C j0).toNat % 8 = 0) (hov : (cellA C j0).toNat + 8 * Lw + 8 < 2 ^ 64)
    (hbits : System.Platform.numBits = 64)
    (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hCp : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hRA : Γ.get kRA = some (cellA C j0)) (hRL : Γ.get kRL = some (BitVec.ofNat 64 (8 * Lw)))
    (hRM : Γ.get kRM = some (BitVec.ofNat 64 (8 * Lw - 16)))
    (t : PState σ) (ht : Inv C s Γ M D t) (hbe : t.be = false) :
    Stop (evaluateHOLFiniteState t topP).1 ∨
      ((∃ w, (evaluateHOLFiniteState t topP).1 = some (.returned (.val (.word w)))) ∧
        ∃ nb bs : List (BitVec 8), nb.length = 8 * Lw ∧
          t.ffi.ioEvents ++ [⟨.extCall fRead, [], bs.zip nb⟩] <+: (evaluateHOLFiniteState t topP).2.ffi.ioEvents ∧
          ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
            ∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP rc.decls.toList
              = .ok (ConLeche.streamEnv rc.decls.toList)) :=
  top_verdict pins pinsP ra C hok hf (front_ok σ C hC) (fold_ok C hC) hs hpl hfe (feed_ok C hC) s hst hoff hpo hpp
    hpins Γ M D hD rb capD jN cap j0 Lw hlay hbuf0 hcells hL16 h59 hal hov hbits hcap1 hcapN hcap8 hcapD8 hZb hZn hTN
    hTL hTE hCp hRB hCD hZL hRA hRL hRM t ht hbe

end ConPanqueque.Code
