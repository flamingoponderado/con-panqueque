import ConPanqueque.Scan.Skip

/-! # `skipWs` and `skipDigits` in Pancake: instances of the skip loop. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

/-- `c == 32 || c == 9 || c == 13`, as a 0/1 word. -/
def wsTest : ExpHOL 64 :=
  .op .or [.cmp .equal (vv sC) (.const 32),
    .op .or [.cmp .equal (vv sC) (.const 9), .cmp .equal (vv sC) (.const 13)]]

/-- `c - 48 < 10` unsigned: `48 ≤ c ≤ 57`. -/
def digitTest : ExpHOL 64 := .cmp .lower (.op .sub [vv sC, .const 48]) (.const 10)

theorem wsTest_ok : TestOK isWsN wsTest := by
  intro σ u c hc h
  have e : ∀ k : Nat, k < 256 → (BitVec.ofNat 64 c == BitVec.ofNat 64 k) = (c == k) := by
    intro k hk
    by_cases hck : c = k
    · subst hck; simp
    · have : BitVec.ofNat 64 c ≠ BitVec.ofNat 64 k := by
        intro e; apply hck; have := congrArg BitVec.toNat e; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr hck]
  have e32 : (BitVec.ofNat 64 c == 32#64) = (c == 32) := e 32 (by decide)
  have e9 : (BitVec.ofNat 64 c == 9#64) = (c == 9) := e 9 (by decide)
  have e13 : (BitVec.ofNat 64 c == 13#64) = (c == 13) := e 13 (by decide)
  simp only [wsTest, evalHOLExact, evalListHOLExact, vv, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    e32, e9, e13]
  have f : ∀ k : Nat, k < 256 → (BitVec.ofNat 64 c = BitVec.ofNat 64 k ↔ c = k) := by
    intro k hk
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  have f32 : (BitVec.ofNat 64 c = 32#64) ↔ c = 32 := f 32 (by decide)
  have f9 : (BitVec.ofNat 64 c = 9#64) ↔ c = 9 := f 9 (by decide)
  have f13 : (BitVec.ofNat 64 c = 13#64) ↔ c = 13 := f 13 (by decide)
  by_cases h32 : c = 32 <;> by_cases h9 : c = 9 <;> by_cases h13 : c = 13 <;>
    simp [h32, h9, h13, f32, f9, f13, isWsN, bw, wordOpHOL, wordOp, valueIsWord, valueWord] <;>
    first | decide | omega

theorem digitTest_ok : TestOK isDigitN digitTest := by
  intro σ u c hc h
  unfold digitTest
  rw [ConsLoop.eval_cmp_of u .lower _ _ (BitVec.ofNat 64 c - 48) 10 (eval_sub_c u sC _ _ h)
    (by simp [evalHOLExact])]
  have : (BitVec.ofNat 64 c - 48 < 10) ↔ (48 ≤ c ∧ c ≤ 57) := by
    have e48 : (48 : BitVec 64).toNat = 48 := rfl
    have e10 : (10 : BitVec 64).toNat = 10 := rfl
    rw [BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_ofNat, e48, e10]
    constructor <;> intro h' <;> omega
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, isDigitN]
  by_cases hd : 48 ≤ c ∧ c ≤ 57
  · simp [hd.1, hd.2]; exact this.mpr hd
  · have hn : ¬ (BitVec.ofNat 64 c - 48 < 10) := fun h' => hd (this.mp h')
    have : ¬ (decide (48 ≤ c) && decide (c ≤ 57)) = true := by simp; omega
    simp [this]; exact BitVec.not_lt.mp hn

section
variable {σ : Type}

/-- **`skipWs` in Pancake is con-leche's `skipWs`**, on a buffer holding the bytes of `b`. -/
theorem skipWs_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    Stop (evaluateHOLFiniteState t (skFun wsTest)).1 ∨
      ((evaluateHOLFiniteState t (skFun wsTest)).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (ConLeche.Frontend.skipWs b i).toNat)))) ∧
        (evaluateHOLFiniteState t (skFun wsTest)).2.memory = t.memory ∧
        (evaluateHOLFiniteState t (skFun wsTest)).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t (skFun wsTest)).2.globals = t.globals ∧
        (evaluateHOLFiniteState t (skFun wsTest)).2.code = t.code) := by
  rw [skipWs_eq hp _ i rfl]
  exact skFun_spec isWsN wsTest wsTest_ok t A b.data.toList i.toNat hb (by simpa using hi) lb
    (by simpa using ln) li

/-- **`skipDigits` in Pancake is con-leche's `skipDigits`**. -/
theorem skipDigits_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    Stop (evaluateHOLFiniteState t (skFun digitTest)).1 ∨
      ((evaluateHOLFiniteState t (skFun digitTest)).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (ConLeche.Frontend.skipDigits b i).toNat)))) ∧
        (evaluateHOLFiniteState t (skFun digitTest)).2.memory = t.memory ∧
        (evaluateHOLFiniteState t (skFun digitTest)).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t (skFun digitTest)).2.globals = t.globals ∧
        (evaluateHOLFiniteState t (skFun digitTest)).2.code = t.code) := by
  rw [skipDigits_eq hp _ i rfl]
  exact skFun_spec isDigitN digitTest digitTest_ok t A b.data.toList i.toNat hb (by simpa using hi) lb
    (by simpa using ln) li

end

end ConPanqueque.Scan
