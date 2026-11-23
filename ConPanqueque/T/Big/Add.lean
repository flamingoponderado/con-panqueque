import ConPanqueque.T.Big.Cmp
import ConPanqueque.T.Big.AddMath
import ConPanqueque.T.Core.ConstVal
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Adding two `Nat` literals

`addCore(x, y)` (the longer first) writes the digits of `x + y` into a fresh heap block: a carry loop over
the shared limbs, one over the rest of `x` (with a zero limb for `y`), the final carry, the length.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def aX := ofString "ax"
def aY := ofString "ay"
def aPa := ofString "apa"
def aLa := ofString "ala"
def aLb := ofString "alb"
def aO := ofString "ao"
def aQa := ofString "aqa"
def aQb := ofString "aqb"
def aQo := ofString "aqo"
def aU := ofString "au"
def aV := ofString "av"
def aS1 := ofString "as1"
def aS := ofString "as"
def aC := ofString "ac"
def aI := ofString "ai"

/-- One digit: `s1 := u + v; s := s1 + c; c := (s1 < u) + (s < s1); [qo] := s`. -/
def digitP : ProgHOL 64 :=
  .seq (.assign .local aS1 (.op .add [vv aU, vv aV]))
  (.seq (.assign .local aS (.op .add [vv aS1, vv aC]))
  (.seq (.assign .local aC (.op .add [.cmp .lower (vv aS1) (vv aU), .cmp .lower (vv aS) (vv aS1)]))
  (.store (vv aQo) (vv aS))))

def addLoop1 : ProgHOL 64 :=
  .while (.cmp .lower (vv aI) (vv aLb))
    (.seq (.assign .local aU (.load .one (vv aQa)))
    (.seq (.assign .local aV (.load .one (vv aQb)))
    (.seq digitP
    (.seq (.assign .local aQa (.op .add [vv aQa, .const 8]))
    (.seq (.assign .local aQb (.op .add [vv aQb, .const 8]))
    (.seq (.assign .local aQo (.op .add [vv aQo, .const 8]))
    (.assign .local aI (.op .add [vv aI, .const 1]))))))))

def addLoop2 : ProgHOL 64 :=
  .while (.cmp .lower (vv aI) (vv aLa))
    (.seq (.assign .local aU (.load .one (vv aQa)))
    (.seq (.assign .local aV (.const 0))
    (.seq digitP
    (.seq (.assign .local aQa (.op .add [vv aQa, .const 8]))
    (.seq (.assign .local aQo (.op .add [vv aQo, .const 8]))
    (.assign .local aI (.op .add [vv aI, .const 1])))))))

def addCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv aX)) (.seq eViewP
  (.seq (.assign .local aPa (vv lRp)) (.seq (.assign .local aLa (.op .sub [vv lRn, .const 1]))
  (.seq (.assign .local lDh (vv aY)) (.seq eViewP
  (.seq (.assign .local aLb (.op .sub [vv lRn, .const 1]))
  (allocP C aO (.panop .mul [.op .add [vv aLa, .const 2], .const 8])
  (.seq (.assign .local aQa (.op .add [vv aPa, .const 8]))
  (.seq (.assign .local aQb (.op .add [vv lRp, .const 8]))
  (.seq (.assign .local aQo (.op .add [vv aO, .const 8]))
  (.seq (.assign .local aC (.const 0)) (.seq (.assign .local aI (.const 0))
  (.seq addLoop1 (.seq addLoop2
  (.seq (.store (vv aQo) (vv aC))
  (.seq (.store (vv aO) (.op .add [vv aLa, vv aC]))
  (.return (vv aO)))))))))))))))))))

def addLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, aPa, aLa, aLb, aO, aQa, aQb, aQo, aU, aV, aS1, aS, aC,
  aI]
def addParams : List MlS := [aX, aY]

def addBody (C : Ctx) : ProgHOL 64 := prologue addLocals (addCore C)

end ConPanqueque.T.Big
