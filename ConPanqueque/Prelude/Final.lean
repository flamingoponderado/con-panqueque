import ConPanqueque.Prelude.HoistDen
import ConPanqueque.Prelude.Text
import ConLeche.Verify.Cached.PureRun

/-! # From the program's parses, passes and fold to con-leche's prepared stream

`final_verdict`: the program parsed the prelude's bytes (`parseBytes` of `builtinPreludeText`'s
UTF-8) to the records `P` and the stream to `Q` in one store; the override pass established `OverW`
and the hoist check `HoistW` of the folded list `P ++ (Q without its prelude copies)`; the twin fold
accepted that list (as `seq_bridge'` gives it).  Then con-leche's built-in prelude parses and its
pure fold accepts the input prepared with it — the form of `checkMainG_ndjson_accept`. -/

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

theorem builtinPreludeE_eq {rP : ParseResultD}
    (h : ConLeche.Frontend.parseBytes builtinPreludeText.toUTF8 = .ok rP) : builtinPreludeE = .ok ⟨rP.decls⟩ := by
  simp only [builtinPreludeE, parseExportD, h]; rfl

/-- **The verdict at con-leche's built-in prelude.** -/
theorem final_verdict {st : EStore} (hwf : StoreWF st) {pinH : Array NIdx} (hp : denoteNL st pinH.toList pinNames)
    {Q P : List IDeclaration} {rc rP : ParseResultD}
    (hrP : ConLeche.Frontend.parseBytes builtinPreludeText.toUTF8 = .ok rP)
    (hQ : denoteDecls st Q = some rc.decls.toList) (hP : denoteDecls st P = some rP.decls.toList)
    (hO : OverW Q P) (hH : HoistW pinH (P ++ Q.filter (keepW (P.map keyOf))))
    {dsP : List Declaration} (hds : denoteDecls st (P ++ Q.filter (keepW (P.map keyOf))) = some dsP)
    (hacc : ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) [] dsP =
      .ok (ConLeche.streamEnv dsP)) :
    ∃ pre, builtinPreludeE = .ok pre ∧
      ∃ E, ConLeche.PureRun [] (preparePrelude pre rc.decls).toList Env.empty E := by
  refine ⟨⟨rP.decls⟩, builtinPreludeE_eq hrP, ?_⟩
  have hk := denoteDecls_keep hwf hQ hP hO
  have hj : denoteDecls st (P ++ Q.filter (keepW (P.map keyOf))) =
      some (joined rP.decls.toList rc.decls.toList) := denoteDecls_append hP hk
  rw [hds] at hj
  have e : dsP = joined rP.decls.toList rc.decls.toList := Option.some.inj hj
  rw [preparePrelude_over ⟨rP.decls⟩ rc.decls (overOK_of_overW hwf hQ hP hO)
    (by rw [← e]; exact hoistOK_of_hoistW hwf hp hds hH), ← e]
  obtain ⟨F, hF⟩ := hacc
  exact ⟨_, ConLeche.PureRun.of_foldlM (pins := []) (F := F) dsP hF⟩

end ConPanqueque.Prelude
