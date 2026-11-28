import ConPanqueque.Start.Main3
import ConLeche.Model.Fold

/-! # What an accepting run means

`main_verdict2` ends at con-leche's pure checker (`checkDeclsPure`, validating mode).  con-leche's
model theorems then apply: the accepted declarations' environment has a set-theoretic model, so in
particular the compiled checker never accepts a stream storing a constant of type `False`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.Logic ConPanqueque.T ConPanqueque.Front

namespace ConPanqueque.Start

universe w

variable {σ : Type}

/-- **If the compiled checker returns, the declarations it read have a model**, and none of them
is a stored constant of type `False`. -/
theorem main_model (V : Type w) [ConLeche.SetTheory V] (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (hbits : System.Platform.numBits = 64) (t : PState σ) (hm : InitMem t) (hg : InitGlobals t codeTP)
    (hbe : t.be = false) (w : BitVec 64)
    (hret : (evaluateHOLFiniteState t mainBody2).1 = some (.returned (.val (.word w)))) :
    ∃ nb bs : List (BitVec 8), ⟨.extCall fRead, [], bs.zip nb⟩ ∈ (evaluateHOLFiniteState t mainBody2).2.ffi.ioEvents ∧
      ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
        Nonempty (ConLeche.Model.EnvModelM V (ConLeche.streamEnv rc.decls.toList)) ∧
        ∀ c ∈ (ConLeche.streamEnv rc.decls.toList).consts,
          c.toConstantVal.type = .const ConLeche.falseName [] → False := by
  rcases main_verdict2 ra hbits t hm hg hbe with hs | ⟨-, nb, bs, -, hev, rc, hrc, ⟨F', hacc⟩, -⟩
  · exact absurd hret (stop_ne_returned hs _)
  exact ⟨nb, bs, hev, rc, hrc, ConLeche.Model.checkDeclsPure_sound_of (V := V) hacc,
    ConLeche.Model.no_proof_of_False_pure V hacc⟩

end ConPanqueque.Start
