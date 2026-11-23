import ConPanqueque.T.Core.WcChain
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfCore`'s tag predicates as expressions

`whnfCoreStuckTag`, `isStuckHead`, `whnfCoreKey`, `whnfCoreCheapSafe` and `whnfCoreStoresDone` are Boolean
functions of handle tags; each is an expression whose value is exactly `boolW` of the twin's answer.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T

def andE (a b : ExpHOL 64) : ExpHOL 64 := .op .and [a, b]
def orE (a b : ExpHOL 64) : ExpHOL 64 := .op .or [a, b]
def notE (a : ExpHOL 64) : ExpHOL 64 := .op .xor [a, .const 1]

theorem sev_andE {Γ : Env} {a b : ExpHOL 64} {x y : Bool} (ha : sev Γ a = some (boolW x))
    (hb : sev Γ b = some (boolW y)) : sev Γ (andE a b) = some (boolW (x && y)) := by
  simp only [andE, sev, ha, hb]; cases x <;> cases y <;> rfl
theorem sev_orE {Γ : Env} {a b : ExpHOL 64} {x y : Bool} (ha : sev Γ a = some (boolW x))
    (hb : sev Γ b = some (boolW y)) : sev Γ (orE a b) = some (boolW (x || y)) := by
  simp only [orE, sev, ha, hb]; cases x <;> cases y <;> rfl
theorem sev_notE {Γ : Env} {a : ExpHOL 64} {x : Bool} (ha : sev Γ a = some (boolW x)) :
    sev Γ (notE a) = some (boolW (!x)) := by
  simp only [notE, sev, ha]; cases x <;> rfl

theorem sev_tagIsB (Γ : Env) (x : MlS) (h : EIdx) (hx : Γ.get x = some (Enc.idxW h)) (k : Nat) (hk : k < 16)
    (hk4 : k ≠ 4) : sev Γ (tagIsE x k) = some (boolW (h.tag == UInt32.ofNat k)) := by
  obtain ⟨w, hw, hiff⟩ := sev_tagIs Γ x h hx k hk hk4
  rw [hw]
  have h01 : w = 0 ∨ w = 1 := by
    simp only [tagIsE, sev, sev_vv, hx] at hw
    simp at hw; split at hw <;> simp_all
  congr 1
  rcases h01 with rfl | rfl
  · have : ¬ h.tag = UInt32.ofNat k := fun e => (hiff.mpr e) rfl
    simp [boolW, this]
  · have : h.tag = UInt32.ofNat k := hiff.mp (by decide)
    simp [boolW, this]

theorem sev_tagIs4B (Γ : Env) (x : MlS) (h : EIdx) (hx : Γ.get x = some (Enc.idxW h)) :
    sev Γ (tagIs4E x) = some (boolW (h.tag == 4)) := by
  obtain ⟨w, hw, hiff⟩ := sev_tagIs4 Γ x h hx
  rw [hw]
  have h01 : w = 0 ∨ w = 1 := by
    simp only [tagIs4E, sev, sev_vv, hx] at hw
    simp at hw
    rw [← hw]
    have hb : ∀ y : BitVec 64, y &&& 1#64 = 0 ∨ y &&& 1#64 = 1 := by
      intro y; rcases Nat.mod_two_eq_zero_or_one y.toNat with h | h
      · left; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and]; omega
      · right; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and]; omega
    split <;> rcases hb (Enc.idxW h >>> (30 : Nat)) with e | e <;> rw [e] <;> decide
  congr 1
  rcases h01 with rfl | rfl
  · have : ¬ h.tag = 4 := fun e => (hiff.mpr e) rfl
    simp [boolW, this]
  · have : h.tag = 4 := hiff.mp (by decide)
    simp [boolW, this]


def stuckTagE (x : MlS) : ExpHOL 64 :=
  notE (orE (tagIs4E x) (orE (tagIsE x 9) (orE (tagIsE x 7) (tagIsE x 0))))
def stuckHeadE (x : MlS) : ExpHOL 64 :=
  orE (tagIsE x 2) (orE (tagIsE x 1) (orE (tagIsE x 6) (orE (tagIsE x 3) (tagIsE x 8))))
def keyE (h e : MlS) : ExpHOL 64 :=
  orE (andE (tagIs4E e) (notE (stuckHeadE h))) (orE (tagIsE e 9) (tagIsE e 7))
def safeE (h e : MlS) : ExpHOL 64 :=
  orE (andE (tagIs4E e) (orE (tagIsE h 5) (stuckHeadE h))) (tagIsE e 7)
def storesDoneE (k e v : MlS) : ExpHOL 64 :=
  orE (andE (tagIs4E e) (andE (vv k) (notE (.cmp .equal (vv v) (vv e))))) (andE (notE (tagIs4E e)) (vv k))

theorem u32_lit (a b : Nat) (ha : a < 16) (hb : b < 16) : (UInt32.ofNat a == UInt32.ofNat b) = decide (a = b) := by
  rcases (by omega : a = b ∨ a ≠ b) with h | h
  · subst h; simp
  · have : UInt32.ofNat a ≠ UInt32.ofNat b := by
      intro e; have := congrArg UInt32.toNat e; simp at this; omega
    simp [this, h]

theorem sev_stuckTag (Γ : Env) (x : MlS) (h : EIdx) (hx : Γ.get x = some (Enc.idxW h)) :
    sev Γ (stuckTagE x) = some (boolW (whnfCoreStuckTag h)) := by
  rw [stuckTagE, sev_notE (sev_orE (sev_tagIs4B Γ x h hx) (sev_orE (sev_tagIsB Γ x h hx 9 (by decide) (by decide))
    (sev_orE (sev_tagIsB Γ x h hx 7 (by decide) (by decide)) (sev_tagIsB Γ x h hx 0 (by decide) (by decide)))))]
  congr 2
  unfold whnfCoreStuckTag
  simp only [ETag.app, ETag.proj, ETag.letE, ETag.bvar]
  by_cases a : h.tag == 4 <;> by_cases b : h.tag == UInt32.ofNat 9 <;> by_cases c : h.tag == UInt32.ofNat 7 <;>
    by_cases d : h.tag == UInt32.ofNat 0 <;> simp_all <;> first | rfl | (subst_vars; decide) | decide

theorem sev_stuckHead (Γ : Env) (x : MlS) (h : EIdx) (hx : Γ.get x = some (Enc.idxW h)) :
    sev Γ (stuckHeadE x) = some (boolW (isStuckHead h)) := by
  rw [stuckHeadE, sev_orE (sev_tagIsB Γ x h hx 2 (by decide) (by decide)) (sev_orE (sev_tagIsB Γ x h hx 1 (by decide)
    (by decide)) (sev_orE (sev_tagIsB Γ x h hx 6 (by decide) (by decide)) (sev_orE (sev_tagIsB Γ x h hx 3 (by decide)
    (by decide)) (sev_tagIsB Γ x h hx 8 (by decide) (by decide)))))]
  congr 2
  unfold isStuckHead
  simp only [ETag.sort, ETag.fvar, ETag.forallE, ETag.const, ETag.lit]
  by_cases a : h.tag == UInt32.ofNat 2 <;> by_cases b : h.tag == UInt32.ofNat 1 <;>
    by_cases c : h.tag == UInt32.ofNat 6 <;> by_cases d : h.tag == UInt32.ofNat 3 <;>
    by_cases f : h.tag == UInt32.ofNat 8 <;> simp_all <;> first | rfl | (subst_vars; decide) | decide

end ConPanqueque.T.WC
