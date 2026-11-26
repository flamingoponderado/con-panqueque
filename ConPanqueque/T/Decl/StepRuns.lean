import ConPanqueque.T.Decl.StepDefn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-! # `checkDeclStep`'s twin runs: the `And` pin test at one name, the per-record flush -/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

theorem andPin_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (n : NIdx) :
    andPinNameFree n s = .ok (!(pinIn C 11 12 n || pinIn C 48 50 n), s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  unfold andPinNameFree andPinNameHs
  simp only [pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO, PIN_AND_REC]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h _ (show 11 < pinCount by decide),
    h _ (show 48 < pinCount by decide), h _ (show 49 < pinCount by decide)]
  simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd, Nat.reduceSub]
  simp only [beq_eq_decide, Bool.not_or]


/-- The flush of `checkDeclStep` (caches, then fresh memos). -/
theorem stepFlush_run (s : AState) :
    (flushCaches >>= fun _ => (get : AM AState) >>= fun s' => set { s' with memos := Memos.empty }) s =
      .ok ((), flushedS true s) := by
  simp [flushCaches, flushedS, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, bind,
    StateT.bind, Except.bind, pure, StateT.pure, Except.pure]


end ConPanqueque.T.Decl
