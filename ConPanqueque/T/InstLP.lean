import ConPanqueque.T.SubstLsTop
import ConPanqueque.T.EIntern2
import ConPanqueque.T.Ex.Abstract1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `instLPGo`: substitute level parameters throughout an expression

`instLP(fu, h, ks, us)`: con-ron's `instLPGo` with the names `ks` a heap block of handles and the
levels `us` a list handle. The `hasLP` cutoff reads bit 0 of the derived word; `sort`/`const` call the
level and level-list substitutions; the other composite arms go through the `instLPC` memo at `(h, 0)`.
-/

namespace ConPanqueque.T.ILP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM
open ConPanqueque.T.LEq ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq ConPanqueque.T.ExA

def fInstLP := ofString "instLPGo"
def ilpParams : List MlS := [pFu, pH, pKp, pUs]

/-- The memo probe at `(h, 0)`, and on a hit its answer. -/
def probedL (G : BitVec 64) (miss : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
  (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (.const 0))
  (.seq (.call (some (some (.local, lX), none)) fMemoGet [.const G, lenE (.const 0)])
    (.ite (vv lX) (.return (.op .sub [vv lX, .const 1])) miss)))

/-- `memo[(h, 0)] := w; return w`. -/
def setRetL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
  (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (.const 0))
  (.seq (.call (some (some (.local, lX), none)) fMemoSet [.const G, lenE (.const 0), vv lW]) (.return (vv lW))))

def callI (x arg : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fInstLP [.op .sub [vv pFu, .const 1], vv arg, vv pKp, vv pUs]

def viewH (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP rest))

def sortI : ProgHOL 64 :=
  viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
  (.seq (.call (some (some (.local, lA2), none)) fSubstLH [vv lA1, vv pKp, vv pUs])
  (.ite (eqE lA2 lA1) (.return (vv pH))
    (.seq (.call (some (some (.local, lW), none)) fInternSort [vv lA2]) (.return (vv lW))))))

def constI : ProgHOL 64 :=
  viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, lA3), none)) fSubstLsH [vv lA2, vv pKp, vv pUs])
  (.ite (eqE lA3 lA2) (.return (vv pH))
    (.seq (.call (some (some (.local, lW), none)) fInternConst [vv lA1, vv lA3]) (.return (vv lW)))))))

def fvarRestI (G : BitVec 64) : ProgHOL 64 :=
  .seq (callI lY lA1)
    (rebuild (eqE lY lA1) (.call (some (some (.local, lW), none)) fInternFVar [vv lY, vv lB]) (setRetL G))

def fvarI (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.const 0)) (fvarRestI G))
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8]))) (fvarRestI G)) hang))))

def binI (G : BitVec 64) (fn : MlS) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callI lY lA1) (.seq (callI lZ lA2)
    (rebuild (.op .and [eqE lY lA1, eqE lZ lA2]) (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ])
      (setRetL G)))))))

def letLP (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (callI lY lA1) (.seq (callI lZ lA2) (.seq (callI lB lA3)
    (rebuild (.op .and [.op .and [eqE lY lA1, eqE lZ lA2], eqE lB lA3])
      (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (setRetL G)))))))))

def projRestI (G : BitVec 64) : ProgHOL 64 :=
  .seq (callI lY lA2)
    (rebuild (eqE lY lA2) (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (setRetL G))

def projI (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestI G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestI G)) hang)))))

def coreI (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
  (.ite (.cmp .equal (.op .and [vv lDo1, .const 1]) (.const 0)) (.return (vv pH))
  (.ite (isAppE (vv pH)) (binI G fInternApp)
  (.ite (tagIsE pH 5) (binI G fInternLam)
  (.ite (tagIsE pH 6) (binI G fInternForallE)
  (.ite (tagIsE pH 1) (fvarI G)
  (.ite (tagIsE pH 7) (letLP G)
  (.ite (tagIsE pH 9) (projI G)
  (.ite (tagIsE pH 2) sortI
  (.ite (tagIsE pH 3) constI (.return (vv pH))))))))))))))

def ilpBody (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreI (C.mG (.e .instLP)))

end ConPanqueque.T.ILP
