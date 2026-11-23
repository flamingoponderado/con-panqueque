import ConPanqueque.T.Comp.DefeqBodyC
import ConPanqueque.T.Comp.InferBodyIOC
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The knot, closed

The five concrete bodies, the code table they need (`AllCodes`), and the knot theorem applied: at every fuel up
to `2^62`, every entry point refines the twin's knot, given only the context's well-formedness and its code table.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

/-- The five bodies. -/
def kBodies : KBodies where
  wc := fun _ => wcbBody
  w := fun _ => WB.wbBody
  i := fun _ => ibBody
  d := bqBody
  io := fun _ => ibioBody
  inv_saved := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  inv_H := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The code table the bodies run on, besides the entries and bodies themselves. -/
structure AllCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  wcE : C.code.lookup fWC = some (pmap wcParams, wcE, .one)
  wb : WbCodes C
  wc : WcAll mode C
  ib : IbAll C
  ibio : IbioAll C
  bq : BqAll mode C

section
variable {σ : Type}

/-- The entries at fuel `n`, at every derived context, from the knot's entry specs. -/
theorem ents_of {mode : ConLeche.CheckMode} {n : Nat} {C : Ctx}
    (hent : EntrySpecs (σ := σ) mode (fun C _ => AllCodes mode C) kBodies n) (hok : CtxOK C)
    (hc : KCodes C kBodies) (hac : AllCodes mode C) : Ents (σ := σ) mode n C := by
  have hE : ∀ (H : List (BitVec 64)) (St : EStore) s, _ := fun H St s =>
    hent (ctxSt (ctxH C H) St) (ctxOK_St (ctxOK_H hok H) St) (by ctx_tr hc) s (by ctx_tr hac)
  exact ⟨fun H St s c d e hd => (hE H St s).1 c d e hd, fun H St s d e hd => (hE H St s).2.1 d e hd,
    fun H St s d e hd => (hE H St s).2.2.1 d e hd, fun H St s d a b hd => (hE H St s).2.2.2.1 d a b hd,
    fun H St s d a b hd => (hE H St s).2.2.2.2.1 d a b hd, fun H St s d e hd => (hE H St s).2.2.2.2.2 d e hd⟩

/-- **Every body refines its twin, from the entries one level down.** -/
theorem kbody (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) :
    ∀ n, n < 2 ^ 62 → EntrySpecs (σ := σ) mode (fun C _ => AllCodes mode C) kBodies n →
      BodySpecs (σ := σ) mode (fun C _ => AllCodes mode C) kBodies n := by
  intro n hn hent C hok hc s hac
  have hE := ents_of hent hok hc hac
  have hn64 : n < 2 ^ 64 := by omega
  refine ⟨fun c d e hd => ?_, fun d e hd => ?_, fun d e hd => ?_, fun d a b hd => ?_, fun d e hd => ?_⟩
  · exact callee_of_pre rfl (wcb_body ra mode n hok hac.wc hn64 hE s c d hd e)
  · exact callee_of_pre rfl (wb_body ra mode n hok hac.wcE hac.wb (fun H s1 d' e' hd' => hE.wc H C.St s1 false d' e' hd')
      (fun H s1 d' e' hd' => hE.w H C.St s1 d' e' hd') s d hd e)
  · exact callee_of_pre rfl (ib_body ra mode n hok hac.ib hn64 hE s d e (by omega))
  · exact callee_of_pre rfl (bq_body ra mode n hok hac.bq hE s d hd a b)
  · exact callee_of_pre rfl (ibio_body ra mode n hok hac.ibio hn64 hE s d e (by omega))

/-- **The knot, closed.** -/
theorem knot_closed (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) :
    ∀ n, n ≤ 2 ^ 62 → EntrySpecs (σ := σ) mode (fun C _ => AllCodes mode C) kBodies n :=
  knot_all mode (fun C _ => AllCodes mode C) kBodies (fun C s _ hac => by ctx_tr hac) (kbody ra mode)

end

end ConPanqueque.T.Comp
