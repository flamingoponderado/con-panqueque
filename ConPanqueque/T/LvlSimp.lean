import ConPanqueque.T.LvlComb
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `simplify`

con-leche's `Level.simplify`: `succ` and `max` normalize their children (`combining` for `max`), and an
`imax` collapses when its left side is `0` or `1` or its right side is `0` or a successor.
-/

namespace ConPanqueque.T.LSimp
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.LComb

def fSimp := ofString "simplify"

/-- With `ls` in `a1` and `rs` in `z`: the right side's shape. -/
def imaxR (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv lZ)) (lvViewP
    (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ))
      (.ite (.cmp .equal (vv lX) (.const 1))
        (.seq (.call (some (some (.local, lW), none)) fComb [vv lA1, vv lZ]) (.return (vv lW)))
        (alloc3 C lW (.const 3) (vv lA1) (vv lZ) (.return (vv lW))))))

/-- The left side `0` or `1` answers `rs`; otherwise the right side decides. -/
def imaxT (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv lA1)) (lvViewP
    (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ))
      (.ite (.cmp .equal (vv lX) (.const 1))
        (.seq (.assign .local lD1 (.load .one (vv lY))) (.seq (.assign .local lQ (vv lD1)) (lvViewP
          (.ite (.cmp .equal (vv lX) (.const 0)) (.return (vv lZ)) (imaxR C)))))
        (imaxR C))))

def simpCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lQ (vv pLa)) (lvViewP
    (.seq (.assign .local lA2 (vv lX)) (.seq (.assign .local lA3 (vv lY))
    (.ite (.cmp .equal (vv lA2) (.const 0)) (.return (vv pLa))
    (.ite (.cmp .equal (vv lA2) (.const 4)) (.return (vv pLa))
    (.seq (.assign .local lD1 (.load .one (vv lA3)))
    (.ite (.cmp .equal (vv lA2) (.const 1))
      (.seq (.call (some (some (.local, lA1), none)) fSimp [vv lD1])
        (alloc2 C lW (.const 1) (vv lA1) (.return (vv lW))))
      (.seq (.assign .local lB (.load .one (.op .add [vv lA3, .const 8])))
      (.seq (.call (some (some (.local, lA1), none)) fSimp [vv lD1])
      (.seq (.call (some (some (.local, lZ), none)) fSimp [vv lB])
      (.ite (.cmp .equal (vv lA2) (.const 2))
        (.seq (.call (some (some (.local, lW), none)) fComb [vv lA1, vv lZ]) (.return (vv lW)))
        (imaxT C))))))))))))

def simpBody (C : Ctx) : ProgHOL 64 := prologue lvlLocals (simpCore C)

/-- The twin's `imax` case after both sides are simplified. -/
def imaxTw (ls rs : ConLeche.Level) : ConLeche.Level :=
  if ls = .zero || ls = .succ .zero then rs
  else match rs with
    | .zero => .zero
    | .succ _ => ConLeche.Level.combining ls rs
    | _ => .imax ls rs

theorem simplify_imax (l r : ConLeche.Level) :
    ConLeche.Level.simplify (.imax l r) = imaxTw (ConLeche.Level.simplify l) (ConLeche.Level.simplify r) := by
  simp only [ConLeche.Level.simplify, imaxTw]
  split <;> rfl

end ConPanqueque.T.LSimp
