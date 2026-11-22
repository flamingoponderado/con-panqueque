import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

example {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n : MlS) (v : ValueHOL 64) :
    (setVarHOLFinite n v s).locals.lookup n = some v := by
  simp [setVarHOLFinite, FUPDATE]
example {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n m : MlS) (v : ValueHOL 64) (h : m ≠ n) :
    (setVarHOLFinite n v s).locals.lookup m = s.locals.lookup m := by
  simp [setVarHOLFinite, FUPDATE, Ne.symm h]
