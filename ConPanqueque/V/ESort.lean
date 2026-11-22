import ConPanqueque.V.EIntern
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The four stores together, and interning `sort u`

`SRep`: the expression store and the three below it (level lists, levels,
names) represented, each with its scratch flag word. `eInternSort`: the key
`[u]`, the level's derived record through the level store, `sortDataE`, then
the intern tail at kind 11.
-/

namespace ConPanqueque.V

structure SRep {σ : Type} (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe : BitVec 64)
    (st : EStore) : Prop where
  e : ERep t L FLe st
  ls : LsRep t L FLs st.lss
  l : LRep t L FLl st.lss.ls
  n : NRep t L FLn st.lss.ls.ns

def lEu := ofString "eu"
def lFll := ofString "fll"
def lFle := ofString "fle"
def lLh := ofString "lh"
def lLpv := ofString "lp"

def eInternSort : ProgHOL 64 :=
  .seq (.store (vv lKb) (vv lEu))
  (.seq (.assign .local lFl (vv lFll))
  (.seq (.assign .local lDh (vv lEu))
  (.seq (storeDerived 3 5)
  (.seq (.assign .local lLh (vv lDo1))
  (.seq (.assign .local lLpv (vv lDo2))
  (.seq (.assign .local lDv ExprData.sortDataE)
  (.seq (.assign .local lDv2 (.const 0))
  (.seq (.assign .local lSk (.cmp .notEqual (.shift .lsr (vv lEu) (.const 31)) (.const 0)))
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lOn (.load .one (vv lFl)))
  (.seq (.assign .local lPg (descK 11 0))
  (.seq (.assign .local lSg (descK 11 1))
  (.seq (.assign .local lK (vv lKb))
  (.seq (.assign .local lL (.const 1))
    internTwo))))))))))))))

section
variable {σ : Type}

theorem erep_sorts {t u : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) (P' Sc' : Tbl SortNode EIdx UInt64)
    (hP : TabAt u L 11 0 Enc.encSort dWN P' (mkN ETag.sort 0)) (hS : TabAt u L 11 1 Enc.encSort dWN Sc' (mkN ETag.sort 1))
    (hfl : u.memory FL = t.memory FL) (hd : u.memaddrs = t.memaddrs)
    (hag : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 11 → Agree L FL t u k tier) :
    ERep u L FL { st with pers := { st.pers with sorts := P' }, scr := { st.scr with sorts := Sc' } } := by
  have A : ∀ k tier, 9 ≤ k → k < 19 → tier < 2 → k ≠ 11 → ∀ {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α]
      [DecidableEq α] {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ}
      {mkI : Nat → ι}, TabAt t L k tier enc dW tb mkI → TabAt u L k tier enc dW tb mkI :=
    fun k tier h1 h2 h3 h4 _ _ _ _ _ _ _ _ _ _ _ hT =>
      tabAt_frame hT (hag k tier h1 h2 h3 h4).1 (hag k tier h1 h2 h3 h4).2 hd
  exact ⟨⟨by rw [hd]; exact h.fl.1, by rw [hfl]; exact h.fl.2⟩,
    A 9 0 (by decide) (by decide) (by decide) (by decide) h.p0, A 10 0 (by decide) (by decide) (by decide) (by decide) h.p1,
    hP, A 12 0 (by decide) (by decide) (by decide) (by decide) h.p3,
    A 13 0 (by decide) (by decide) (by decide) (by decide) h.p4, A 14 0 (by decide) (by decide) (by decide) (by decide) h.p5,
    A 15 0 (by decide) (by decide) (by decide) (by decide) h.p6, A 16 0 (by decide) (by decide) (by decide) (by decide) h.p7,
    A 17 0 (by decide) (by decide) (by decide) (by decide) h.p8, A 18 0 (by decide) (by decide) (by decide) (by decide) h.p9,
    A 9 1 (by decide) (by decide) (by decide) (by decide) h.s0, A 10 1 (by decide) (by decide) (by decide) (by decide) h.s1,
    hS, A 12 1 (by decide) (by decide) (by decide) (by decide) h.s3,
    A 13 1 (by decide) (by decide) (by decide) (by decide) h.s4, A 14 1 (by decide) (by decide) (by decide) (by decide) h.s5,
    A 15 1 (by decide) (by decide) (by decide) (by decide) h.s6, A 16 1 (by decide) (by decide) (by decide) (by decide) h.s7,
    A 17 1 (by decide) (by decide) (by decide) (by decide) h.s8, A 18 1 (by decide) (by decide) (by decide) (by decide) h.s9⟩

end

end ConPanqueque.V
