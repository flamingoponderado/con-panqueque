import ConPanqueque.ExprFold
import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Fold ConPanqueque.Table

namespace ConPanqueque.MemoFold

def nTbl := ofString "tbl"
def nTlim := ofString "tlim"

/-- The memoized function: look `u` up; on a miss call `fr` (the raw fold, whose
recursive calls go to this function), insert the result, return it. -/
def memoBody (fr : MlS) : ProgHOL 64 :=
  .dec nT .one (.var .global nTbl)
  (.dec nK .one (.var .local nU)
  (.dec nL .one (.var .global nTlim)
  (.dec nJ .one (.const 0)
  (.dec nR .one (.const 0)
  (.dec nG .one (.const 1)
  (.seq scanLoop
    (.ite (.cmp .equal (vv nJ) (vv nL))
      (.dec nV .one (.const 0)
        (.seq (.call (some (some (.local, nV), none)) fr [.var .local nU])
          (.seq (.assign .local nJ (.const 0))
            (.seq (.assign .local nG (.const 1))
              (.dec nO .one (.const 0)
                (.seq insLoop (.return (vv nV))))))))
      (.return (vv nR)))))))))

/-- The memo invariant: the table (at `tb`, `n` slots) and the arena are disjoint parts
of memory, and every entry stores `f` of the expression at its key. -/
def MemoInv {σ : Type} (h : Heap) (f : ConLeche.Expr → UInt64) (tb : BitVec 64) (n : Nat)
    (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.globals.lookup nTbl = some (.val (.word tb)) ∧
  t.globals.lookup nTlim = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
  ∃ slots : List (BitVec 64 × BitVec 64), slots.length = n ∧ Sat t (TableAt tb slots ∗ (· = h)) ∧
    ∀ kv ∈ slots, kv.1 ≠ 0 → ∃ e, ExprAt h kv.1 e ∧ kv.2 = (f e).toBitVec

theorem memoInv_inMem {σ : Type} {h : Heap} {f : ConLeche.Expr → UInt64} {tb : BitVec 64} {n : Nat}
    {t : PanSemStateFiniteExact 64 σ} (hj : MemoInv h f tb n t) : InMem t h := by
  obtain ⟨_, _, slots, _, ⟨hh, ⟨h1, h2, hd, he, _, rfl⟩, hm⟩, _⟩ := hj
  intro a w ha
  apply hm a w
  subst he
  rcases hd a with e1 | e2
  · simp [union, e1, ha]
  · rw [e2] at ha; cases ha

theorem memoInv_memDet {σ : Type} (h : Heap) (f : ConLeche.Expr → UInt64) (tb : BitVec 64) (n : Nat) :
    MemDet (MemoInv (σ := σ) h f tb n) := by
  intro t t' hm hd hg ⟨g1, g2, slots, hl, hs, hc⟩
  refine ⟨by rw [hg]; exact g1, by rw [hg]; exact g2, slots, hl, ?_, hc⟩
  obtain ⟨hh, hp, hhm⟩ := hs
  exact ⟨hh, hp, fun a w ha => by rw [hm, hd]; exact hhm a w ha⟩

end ConPanqueque.MemoFold

namespace ConPanqueque.Table

theorem insSlots_mem (k v : BitVec 64) : ∀ (slots sl' : List (BitVec 64 × BitVec 64)),
    insSlots k v slots = some sl' → ∀ kv ∈ sl', kv ∈ slots ∨ kv = (k, v)
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, sl', h => by
    simp only [insSlots] at h
    split at h
    · cases h; intro kv hkv; simp at hkv
      rcases hkv with rfl | hkv
      · right; rfl
      · left; simp [hkv]
    · cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r =>
        simp [e] at h; subst h
        intro kv hkv; simp at hkv
        rcases hkv with rfl | hkv
        · left; simp
        · rcases insSlots_mem k v rest r e kv hkv with h1 | h1
          · left; simp [h1]
          · right; exact h1

end ConPanqueque.Table
