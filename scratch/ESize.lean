import ConPanqueque.ExprFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Fold ConPanqueque.ExprFold

namespace ConPanqueque.ExprFold

/-- The number of nodes of an expression (as a tree, wrapping). -/
def size : ConLeche.Expr → UInt64
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 1
  | .fvar _ ty | .proj _ _ ty => size ty + 1
  | .app a b | .lam a b | .forallE a b => size a + size b + 1
  | .letE a b c => size a + size b + size c + 1

def vA : ExpHOL 64 := .var .local nA
def vB : ExpHOL 64 := .var .local nB
def vC : ExpHOL 64 := .var .local nC

def sizeG : Fin 10 → ExpHOL 64
  | 0 | 2 | 3 | 8 => .const 1
  | 1 | 9 => .op .add [vA, .const 1]
  | 4 | 5 | 6 => .op .add [vA, vB, .const 1]
  | 7 => .op .add [vA, vB, vC, .const 1]

theorem size_spec : ExprFoldSpec sizeG size := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [EvW, Lv, sizeG, size, vA, vB, vC, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord,
      valueWord, BitVec.add_assoc]

/-- Node counting in Pancake, as an instance of the expression fold template. -/
theorem size_pancake {σ : Type} (fn : MlS) (h : Heap) {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e)
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code.lookup fn = some ([(nU, .one)], body fn sizeG, .one))
    (hm : InMem s h) (hu : s.locals.lookup nU = some (.val (.word p))) (hck : cost e ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (body fn sizeG) = (some (.returned (.val (.word (size e).toBitVec))), st) ∧
      Post s st (cost e) :=
  fold_spec fn sizeG size size_spec h he s hc hm hu hck

end ConPanqueque.ExprFold
