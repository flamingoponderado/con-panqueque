import ConPanqueque.ConsIns
import ConPanqueque.ConsTbl
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop ConPanqueque.ConsIns ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Interning an `app` node into one tier

The twin's per-tier step (`ETables.find?` then `ETables.push` at the `app`
constructor): on a hit the existing handle, on a miss the node appended with
handle `mkWide tier size`. In Pancake: the probe loop, then the hit's handle
or the append. The key is the record's two handle words; its home slot is
`(f·M + a) & mask`, a hash computed in Pancake (any function serves
correctness).
-/

namespace ConPanqueque.ConsIntern

/-- An `app` record as two words: its handles' words. -/
def encApp (x : AppNode) : BitVec 64 × BitVec 64 := (x.f.word.toUInt64.toBitVec, x.a.word.toUInt64.toBitVec)

theorem encApp_inj : ∀ x y : AppNode, encApp x = encApp y → x = y := by
  intro ⟨⟨f1⟩, ⟨a1⟩⟩ ⟨⟨f2⟩, ⟨a2⟩⟩ h
  simp only [encApp, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : f1 = f2 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h1; simpa using this
  have e2 : a1 = a2 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h2; simpa using this
  subst e1; subst e2; rfl

/-- The home slot: a multiplicative hash of the two words, masked to `n = 2^b` slots. -/
def homeApp (b : Nat) (x : AppNode) : Nat :=
  ((encApp x).1 * 0x9e3779b97f4a7c15#64 + (encApp x).2).toNat % 2 ^ b

/-- The twin's per-tier `app` intern: the cons probe, then on a miss the append with handle
`mkWide tier size` (the `app` arms of `ETables.find?` and `ETables.push`). -/
def tierApp (tb : Tbl AppNode EIdx UInt64) (x : AppNode) (d : UInt64) (tier : UInt32) :
    Tbl AppNode EIdx UInt64 × EIdx :=
  match tb.find? x with
  | some h => (tb, h)
  | none => (tb.push x d (Idx.mkWide tier (UInt32.ofNat tb.size)), Idx.mkWide tier (UInt32.ofNat tb.size))

def lTier := ofString "ctier"
def lI := ofString "ci"
def vv (n : MlS) : ExpHOL 64 := .var .local n

/-- A wide handle's word from the tier and an index expression. -/
def hwE (idx : ExpHOL 64) : ExpHOL 64 :=
  .op .add [.panop .mul [vv lTier, .const 2147483648], .const 1073741824, idx]

def homeE : ExpHOL 64 :=
  .op .and [.op .add [.panop .mul [vv lKf, .const 0x9e3779b97f4a7c15#64], vv lKa], vv lM]

/-- The per-tier `app` intern in Pancake. -/
def internTier : ProgHOL 64 :=
  .dec lJ .one homeE (.dec lC .one (.op .add [vv lM, .const 1])
   (.dec lG .one (.const 1) (.dec lRes .one (.const 0) (.dec lV .one (.const 0)
    (.seq probeLoop
     (.ite (.cmp .notEqual (vv lRes) (.const 0)) (.return (hwE (.op .sub [vv lRes, .const 1])))
      (.ite (.cmp .equal (vv lC) (.const 0)) hang
       (.dec lI .one (.load .one (vv lC0)) (.seq insBody (.return (hwE (vv lI))))))))))))

theorem home_mask (w : BitVec 64) (b : Nat) (hb : b ≤ 56) :
    w &&& BitVec.ofNat 64 (2 ^ b - 1) = BitVec.ofNat 64 (w.toNat % 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ b ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hb
  have h2 : (2 : Nat) ^ 56 < 2 ^ 64 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 ^ b - 1) (by omega),
    Nat.mod_eq_of_lt (a := w.toNat % 2 ^ b) (by have := Nat.mod_lt w.toNat (Nat.two_pow_pos b); omega)]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat b

/-- The table geometry and inputs `internTier` reads from its locals. -/
structure Locals {σ : Type} (t : PanSemStateFiniteExact 64 σ) (x : AppNode) (n cap : Nat) (C S R D dv tier : BitVec 64) :
    Prop where
  kf : t.locals.lookup lKf = some (.val (.word (encApp x).1))
  ka : t.locals.lookup lKa = some (.val (.word (encApp x).2))
  s : t.locals.lookup lS = some (.val (.word S))
  r : t.locals.lookup lR = some (.val (.word R))
  m : t.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1))))
  d : t.locals.lookup lD = some (.val (.word D))
  c : t.locals.lookup lC0 = some (.val (.word C))
  cap : t.locals.lookup lCap = some (.val (.word (BitVec.ofNat 64 cap)))
  dv : t.locals.lookup lDv = some (.val (.word dv))
  tier : t.locals.lookup lTier = some (.val (.word tier))

theorem mkWide_word (tier : UInt32) (i : Nat) (ht : tier ≤ 1) (hi : i < 2 ^ 30) :
    (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec =
      tier.toUInt64.toBitVec * 2147483648 + 1073741824 + BitVec.ofNat 64 i := by
  have ht' : tier.toNat ≤ 1 := by simpa [UInt32.le_iff_toNat_le] using ht
  have hw : (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toNat = tier.toNat * 2147483648 + 1073741824 + i := by
    show (tier * 2147483648 + 1073741824 + UInt32.ofNat i).toNat = _
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rcases (by omega : tier.toNat = 0 ∨ tier.toNat = 1) with h | h <;> rw [h] <;> omega
  apply BitVec.eq_of_toNat_eq
  have e1 : (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toUInt64.toBitVec.toNat =
      (Idx.mkWide (k := .expr) tier (UInt32.ofNat i)).word.toNat := by simp
  have e2 : tier.toUInt64.toBitVec.toNat = tier.toNat := by simp
  have l1 : (2147483648 : BitVec 64).toNat = 2147483648 := rfl
  have l2 : (1073741824 : BitVec 64).toNat = 1073741824 := rfl
  have l3 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  rw [e1, hw, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, e2, l1, l2, l3]
  rcases (by omega : tier.toNat = 0 ∨ tier.toNat = 1) with h | h <;> rw [h] <;> omega

end ConPanqueque.ConsIntern
