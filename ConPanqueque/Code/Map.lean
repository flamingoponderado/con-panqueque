import ConPanqueque.Code.Table

/-! # The code map and its lookups -/

open Flapjack Flapjack.Pancake.PanLang

namespace ConPanqueque.Code

/-- A finite map from an association list (first entry wins). -/
noncomputable def codeMap {V : Type} (l : List (MlS × V)) : HolFiniteMapExact MlS V :=
  ⟨fun k => l.lookup k, ⟨l.map Prod.fst, fun k h => by
    induction l with
    | nil => simp [List.lookup] at h
    | cons p l ih =>
      obtain ⟨k', v⟩ := p
      simp only [List.lookup] at h
      by_cases e : k = k'
      · subst e; simp
      · have : (k == k') = false := by simp [e]
        rw [this] at h; simp only at h; exact List.mem_cons_of_mem _ (ih h)⟩⟩

theorem codeMap_lookup {V : Type} (l : List (MlS × V)) (k : MlS) : (codeMap l).lookup k = l.lookup k := rfl

set_option hygiene false in
/-- Split code-requirement structures and close each lookup from the table. -/
macro "code_auto" : tactic => `(tactic| repeat' (first
  | (first | (rw [‹_ = C.code›]) | skip); rw [hC, codeMap_lookup]; rfl
  | (intro (o : ConPanqueque.T.Big.BitOp); cases o)
  | (intro (b : Bool); cases b)
  | (intro (k : Nat) hk; rcases k with _ | _ | _ | _ | _ | _ | k <;> (try omega))
  | (intro _)
  | (constructor)))

set_option maxRecDepth 100000 in
theorem lvl_ok (C : ConPanqueque.T.Ctx) (hC : C.code = codeMap (codeEntries C)) : ConPanqueque.T.Decl.LvlCodes C := by
  code_auto

end ConPanqueque.Code
