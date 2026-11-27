import ConPanqueque.Prelude.Front
import ConPanqueque.Prelude.Hoist

/-! # con-leche's `preparePrelude` at an accepted overlap and an in-time ground

`preparePrelude_over`: when the stream's prelude copies are the prelude's records (`OverOK`) and
every operation's ground is declared in time in the joined list (`HoistOK`), the prepared stream is
the prelude followed by the stream without its prelude copies — the list the program folds. -/

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

/-- The list the program folds: the prelude, then the stream without its prelude copies. -/
def joined (ps : List Declaration) (ds : List Declaration) : List Declaration :=
  ps ++ ds.filter (keep ps)

theorem preparePrelude_over (pre : PreludeIx) (ds : Array Declaration)
    (hO : OverOK pre.decls.toList ds.toList)
    (hH : HoistOK (joined pre.decls.toList ds.toList).toArray) :
    (preparePrelude pre ds).toList = joined pre.decls.toList ds.toList := by
  obtain ⟨f1, f2⟩ := frontOf_over pre.decls.toList ds hO
  have e : (frontOf #[] pre.decls.toList ds).1 ++ (frontOf #[] pre.decls.toList ds).2 =
      (joined pre.decls.toList ds.toList).toArray := by
    apply Array.ext'; simp only [Array.toList_append, f1, f2, joined]
  unfold preparePrelude prepareD
  simp only [hoistNatOpGround]
  rw [e, hoistTargets_ok _ _ hH]
  simp

end ConPanqueque.Prelude
