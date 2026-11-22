import ConPanqueque.Fold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic

namespace ConPanqueque.Fold

def nTg := ofString "tg"

/-- `if tg == c₁ then p₁ else if tg == c₂ then p₂ … else dflt`. -/
def iteChain : List (BitVec 64 × ProgHOL 64) → ProgHOL 64 → ProgHOL 64
  | [], dflt => dflt
  | (c, p) :: rest, dflt => .ite (.cmp .equal (.var .local nTg) (.const c)) p (iteChain rest dflt)

/-- The first case whose tag matches. -/
def pick (tv : BitVec 64) : List (BitVec 64 × ProgHOL 64) → ProgHOL 64 → ProgHOL 64
  | [], dflt => dflt
  | (c, p) :: rest, dflt => if c = tv then p else pick tv rest dflt

theorem iteChain_eval {σ : Type} (s : PanSemStateFiniteExact 64 σ) (tv : BitVec 64)
    (htg : s.locals.lookup nTg = some (.val (.word tv))) :
    ∀ (cases : List (BitVec 64 × ProgHOL 64)) (dflt : ProgHOL 64),
      evaluateHOLFiniteState s (iteChain cases dflt) = evaluateHOLFiniteState s (pick tv cases dflt)
  | [], _ => rfl
  | (c, p) :: rest, dflt => by
    simp only [iteChain, pick]
    by_cases e : c = tv
    · subst e
      rw [ite_word s _ _ _ 1 (by simp [evalHOLExact, htg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      simp
    · rw [ite_word s _ _ _ 0 (by simp [evalHOLExact, htg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Ne.symm e])]
      simp [e, iteChain_eval s tv htg rest dflt]

end ConPanqueque.Fold
