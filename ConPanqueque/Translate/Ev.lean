import ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-!
# Compositional evaluation lemmas for translated expressions

`PEv s e w`: in state `s`, the expression `e` evaluates to the word `w`. One lemma
per operator the translator emits, so a translated expression's proof is a term
of the same shape as the expression (linear in its size), not one big `simp`.
-/

namespace ConPanqueque.Translate

@[reducible] def PEv {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (w : UInt64) : Prop :=
  @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word w.toBitVec))

variable {σ : Type} {s : PanSemStateFiniteExact 64 σ}

theorem ev_var {x : MlS} {w : UInt64} (h : s.locals.lookup x = some (.val (.word w.toBitVec))) :
    PEv s (.var .local x) w := by
  simp [PEv, evalHOLExact, h]

theorem ev_lit (s : PanSemStateFiniteExact 64 σ) (n : Nat) :
    PEv s (.const (BitVec.ofNat 64 n)) (OfNat.ofNat n) := by
  simp [PEv, evalHOLExact]

theorem ev_add {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .add [a, b]) (x + y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at *

theorem ev_sub {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .sub [a, b]) (x - y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at *

theorem ev_xor {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .xor [a, b]) (x ^^^ y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at *

theorem ev_and {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .and [a, b]) (x &&& y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at *
  change x.toBitVec &&& (y.toBitVec &&& 18446744073709551615#64) = _
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]

theorem ev_or {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .or [a, b]) (x ||| y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at *
  change x.toBitVec ||| (y.toBitVec ||| 0#64) = _
  rw [BitVec.or_zero]

theorem ev_mul {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.panop .mul [a, b]) (x * y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, panOpHOL, valueIsWord, valueWord] at *

theorem ev_shr {a : ExpHOL 64} {x : UInt64} (k : Nat) (hk : k < 64) (ha : PEv s a x) :
    PEv s (.shift .lsr a (.const (BitVec.ofNat 64 k))) (x >>> (OfNat.ofNat k)) := by
  simp [PEv, evalHOLExact, ha, wordShiftHOL] at *
  refine ⟨fun _ => by omega, ?_⟩
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk]

theorem ev_shl {a : ExpHOL 64} {x : UInt64} (k : Nat) (hk : k < 64) (ha : PEv s a x) :
    PEv s (.shift .lsl a (.const (BitVec.ofNat 64 k))) (x <<< (OfNat.ofNat k)) := by
  simp [PEv, evalHOLExact, ha, wordShiftHOL] at *
  refine ⟨fun _ => by omega, ?_⟩
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk]

theorem ev_div {a : ExpHOL 64} {x : UInt64} (k n : Nat) (hk : k < 64) (hn : n = 2 ^ k) (ha : PEv s a x) :
    PEv s (.shift .lsr a (.const (BitVec.ofNat 64 k))) (x / (OfNat.ofNat n)) := by
  simp [PEv, evalHOLExact, ha, wordShiftHOL] at *
  refine ⟨fun _ => by omega, ?_⟩
  rw [Nat.mod_eq_of_lt (by omega)]
  subst hn
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h2]

theorem ev_mod {a : ExpHOL 64} {x : UInt64} (k n j : Nat) (hk : 0 < k) (hk' : k < 64) (hn : n = 2 ^ k)
    (hj : j = 64 - k) (ha : PEv s a x) :
    PEv s (.shift .lsr (.shift .lsl a (.const (BitVec.ofNat 64 j))) (.const (BitVec.ofNat 64 j)))
      (x % (OfNat.ofNat n)) := by
  simp [PEv, evalHOLExact, ha, wordShiftHOL] at *
  subst hn hj
  have hj' : (64 - k) % 18446744073709551616 = 64 - k := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk'
  have hjl : (BitVec.ofNat 64 (64 - k)).toNat = 64 - k := by simp; omega
  simp [hj', hjl, show ¬ 64 ≤ 64 - k from by omega]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_umod, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h2]
  have e : (18446744073709551616 : Nat) = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  rw [e, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem ev_mod1 (s : PanSemStateFiniteExact 64 σ) (x : UInt64) :
    PEv s (.const (BitVec.ofNat 64 0)) (x % 1) := by
  simp [PEv, evalHOLExact]

theorem ev_mix {a b : ExpHOL 64} {x y : UInt64} (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (ConPanqueque.Hash.mixExp a b) (ConPanqueque.Hash.leanMixHash x y) :=
  ConPanqueque.Hash.eval_mixExp s a b x y ha hb

/-- `if c then x else y` as `y + (x - y)·[c]`, for a comparison `c` evaluated to `0`/`1`. -/
theorem ev_ite_core {a b c : ExpHOL 64} {x y : UInt64} (p : Prop) [Decidable p] (ha : PEv s a x) (hb : PEv s b y)
    (hc : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c =
      some (.val (.word (if p then 1 else 0)))) :
    PEv s (.op .add [b, .panop .mul [.op .sub [a, b], c]]) (if p then x else y) := by
  simp [PEv, evalHOLExact, evalListHOLExact, ha, hb, hc, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord] at *
  by_cases hp : p <;> simp [hp] <;> bv_omega

theorem ev_ite_lt {a b p q : ExpHOL 64} {x y u v : UInt64} (hp : PEv s p u) (hq : PEv s q v)
    (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .add [b, .panop .mul [.op .sub [a, b], .cmp .lower p q]]) (if u < v then x else y) := by
  apply ev_ite_core _ ha hb
  simp [evalHOLExact, hp, hq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, UInt64.lt_iff_toBitVec_lt] at *

theorem ev_ite_le {a b p q : ExpHOL 64} {x y u v : UInt64} (hp : PEv s p u) (hq : PEv s q v)
    (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .add [b, .panop .mul [.op .sub [a, b], .cmp .notLower q p]]) (if u ≤ v then x else y) := by
  apply ev_ite_core _ ha hb
  simp [evalHOLExact, hp, hq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, UInt64.le_iff_toBitVec_le] at *

theorem ev_ite_eq {a b p q : ExpHOL 64} {x y u v : UInt64} (hp : PEv s p u) (hq : PEv s q v)
    (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .add [b, .panop .mul [.op .sub [a, b], .cmp .equal p q]]) (if u = v then x else y) := by
  apply ev_ite_core _ ha hb
  simp [evalHOLExact, hp, hq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at *
  by_cases h : u = v <;> simp [h, UInt64.toBitVec_inj]

theorem ev_ite_ne {a b p q : ExpHOL 64} {x y u v : UInt64} (hp : PEv s p u) (hq : PEv s q v)
    (ha : PEv s a x) (hb : PEv s b y) :
    PEv s (.op .add [b, .panop .mul [.op .sub [a, b], .cmp .notEqual p q]]) (if u ≠ v then x else y) := by
  apply ev_ite_core _ ha hb
  simp [evalHOLExact, hp, hq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at *
  by_cases h : u = v <;> simp [h, UInt64.toBitVec_inj]

end ConPanqueque.Translate
