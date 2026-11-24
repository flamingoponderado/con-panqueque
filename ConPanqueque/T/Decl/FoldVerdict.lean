import ConPanqueque.T.Decl.Start
import ConPanqueque.Bridge.SeqFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-! # The fold's verdict

The Pancake fold over a block of value records, started at the driver's index, either stops (out of
fuel or space, or a rejected record: `rejectP`) or returns; when it returns, con-leche's pure fold
accepts the stream the records denote.  This is `checkDeclsPure_spec` (Pancake ⊑ twin) composed with
`Bridge.seq_bridge'` (twin accept ⇒ con-leche accept). -/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

variable {σ : Type}

theorem fold_verdict (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (rs : List (Nat × IDeclaration)) (ob : Nat)
    (hlenR : rs.length < 2 ^ 62) (C : Ctx) (s : AState) (hok : CtxOK C)
    (hc : FoldCodes .verified C) (hs : C.side = false) (hpl : C.saved = none)
    (hfe : C.fe = feStart C.pins) (hp : s.pins = C.pins)
    (hb : BlkAt C.H ob (rs.map (fun r => cellA C r.1)))
    (hrec : ∀ j (hj : j < rs.length), RecOK C rs[j].1 rs[j].2)
    {dsP : List ConLeche.Declaration}
    (hst : StateOK s) (hpo : PinsOK s) (hpp : PersPins s)
    (hpins : PinsDenote s.store pins pinsP)
    (hden : denoteDecls s.store (rs.map Prod.snd) = some dsP)
    (hval : ∀ pd ∈ rs.map Prod.snd, ConPanqueque.Bridge.IsValueDecl pd)
    (t : PState σ)
    (ht : Pre C s (foParams.zip [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 rs.length]) t) :
    Stop (evaluateHOLFiniteState t foldBody).1 ∨
      ((∃ w, (evaluateHOLFiniteState t foldBody).1 = some (.returned (.val (.word w)))) ∧
        ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
          = .ok (ConLeche.streamEnv dsP)) := by
  rcases checkDeclsPure_spec (σ := σ) .verified pins ra rs ob hlenR C s hok hc hs hpl hfe hp hb hrec t ht
    with hstop | ⟨w, hw, a, s', hm, -⟩
  · exact Or.inl hstop
  · exact Or.inr ⟨⟨w, hw⟩, ConPanqueque.Bridge.seq_bridge' hst hpo hpp hpins hden hval hm⟩

end ConPanqueque.T.Decl
