import ConPanqueque.Scan.SkipWs

/-! # `numEnd` in Pancake

The end of a JSON number at `i`: `skipDigits`, then JSON's leading-zero rule.  The first scanner
function that calls another (`call3_ret`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def fSkipDigits := ofString "skipDigits"
def sE2 := ofString "e"

/-- The code-table entry `skipDigits(b, n, i)`. -/
def SkipDigitsCode {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code.lookup fSkipDigits = some ([(sB, .one), (sN, .one), (sI, .one)], skFun digitTest, .one)

def neFun : ProgHOL 64 :=
  .dec sE2 .one (.const 0)
    (.seq (.call (some (some (.local, sE2), none)) fSkipDigits [vv sB, vv sN, vv sI])
      (.ite (.cmp .equal (vv sE2) (vv sI)) (.return (vv sI))
        (.dec sC .one (.loadByte (.op .add [vv sB, vv sI]))
          (.ite (.op .and [.cmp .equal (vv sC) (.const 48),
                .cmp .notEqual (vv sE2) (.op .add [vv sI, .const 1])])
            (.return (vv sI)) (.return (vv sE2))))))

section
variable {σ : Type}

theorem ofNat_inj (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro e; have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    exact this
  · intro e; rw [e]

/-- Returning a local's word: the result, and the frame of the state returned from. -/
theorem return_vv (u : PanSemStateFiniteExact 64 σ) (x : MlS) (w : BitVec 64)
    (h : u.locals.lookup x = some (.val (.word w))) :
    (evaluateHOLFiniteState u (.return (vv x))).1 = some (.returned (.val (.word w))) ∧
    (evaluateHOLFiniteState u (.return (vv x))).2.memory = u.memory ∧
    (evaluateHOLFiniteState u (.return (vv x))).2.memaddrs = u.memaddrs ∧
    (evaluateHOLFiniteState u (.return (vv x))).2.globals = u.globals ∧
    (evaluateHOLFiniteState u (.return (vv x))).2.code = u.code ∧
    (evaluateHOLFiniteState u (.return (vv x))).2.be = u.be := by
  rw [evaluateHOLFiniteState_eq_evaluate_def u (.return _)]
  simp [eval_vv u x _ h, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
    emptyLocalsHOLFinite]

theorem neFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (hi : i0 ≤ bs.length) (hc : SkipDigitsCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    RetSpec t neFun (BitVec.ofNat 64 (numEndL bs i0)) := by
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  have hle := skipL_le_length isDigitN bs _ i0 rfl hi
  have hge := skipL_ge isDigitN bs _ i0 rfl
  unfold RetSpec neFun
  rw [dec_word_eq t sE2 _ 0 _ (by simp [evalHOLExact])]
  let t1 := setVarHOLFinite sE2 (.val (.word 0)) t
  have hcall := call3_ret t1 sE2 fSkipDigits sB sN sI (skFun digitTest) (vv sB) (vv sN) (vv sI) A
    (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 i0) (BitVec.ofNat 64 (skipDigitsL bs i0)) 0
    (by decide) (by decide) (by decide) hc (eval_vv t1 sB _ (by lk [t1]; exact lb))
    (eval_vv t1 sN _ (by lk [t1]; exact ln)) (eval_vv t1 sI _ (by lk [t1]; exact li)) (by lk [t1])
    (fun callee h1 h2 h3 => skFun_spec isDigitN digitTest digitTest_ok _ A bs i0
      (bytesAt_congr hb rfl rfl rfl) hi h1 h2 h3)
  rcases hcall with hs | ⟨u, hu, m1, d1, g1, c1, b1, le1, lo1⟩
  · left; exact seq_stop t1 _ _ hs
  rw [seq_normal _ hu]
  have li1 : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0))) := by
    rw [lo1 sI (by decide)]; lk [t1]; exact li
  have lb1 : u.locals.lookup sB = some (.val (.word A)) := by rw [lo1 sB (by decide)]; lk [t1]; exact lb
  have heq := ConsLoop.eval_cmp_of u .equal (vv sE2) (vv sI) _ _ (eval_vv u sE2 _ le1) (eval_vv u sI _ li1)
  rw [ite_word u _ _ _ _ heq]
  by_cases hei : skipDigitsL bs i0 = i0
  · have : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (skipDigitsL bs i0))
        (BitVec.ofNat 64 i0) = true := by simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hei]
    simp only [this, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u sI _ li1
    have hv : numEndL bs i0 = i0 := by simp [numEndL, hei]
    right; refine ⟨by rw [r1, hv], ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [r2, r3, r4, r5, r6, m1, d1, g1, c1, b1] <;> rfl
  · have : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (skipDigitsL bs i0))
        (BitVec.ofNat 64 i0) = false := by
      have hne : ¬ BitVec.ofNat 64 (skipDigitsL bs i0) = BitVec.ofNat 64 i0 :=
        fun h => hei ((ofNat_inj _ _ (by simp only [skipDigitsL]; omega) (by omega)).mp h)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]
    simp only [this, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    have hlt : i0 < bs.length := by simp only [skipDigitsL] at hei; omega
    have hbu : BytesAt u A bs := bytesAt_congr hb m1 d1 b1
    have haddr : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 i0))) := by
      simp [vv, evalHOLExact, evalListHOLExact, lb1, li1, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [dec_word_eq u sC _ _ _ (eval_loadByte_bytes u _ A bs i0 hbu hlt haddr)]
    let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 bs[i0].toNat))) u
    have lc2 : u2.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 bs[i0].toNat))) := by lk [u2]
    have le2 : u2.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 (skipDigitsL bs i0)))) := by
      lk [u2]; exact le1
    have li2 : u2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0))) := by lk [u2]; exact li1
    have hbyte : bs[i0].toNat < 256 := UInt8.toNat_lt _
    have hand : @evalHOLExact 64 σ _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
        (.op .and [.cmp .equal (vv sC) (.const 48), .cmp .notEqual (vv sE2) (.op .add [vv sI, .const 1])]) =
        some (.val (.word (bw (bs[i0].toNat = 48 ∧ skipDigitsL bs i0 ≠ i0 + 1)))) := by
      have h1 := ConsLoop.eval_cmp_of u2 .equal (vv sC) (.const 48) _ (BitVec.ofNat 64 48)
        (eval_vv u2 sC _ lc2) (by simp [evalHOLExact])
      have h2 := ConsLoop.eval_cmp_of u2 .notEqual (vv sE2) (.op .add [vv sI, .const 1]) _
        (BitVec.ofNat 64 (i0 + 1)) (eval_vv u2 sE2 _ le2)
        (by rw [eval_add_c u2 sI _ _ li2]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
      rw [evalHOLExact]
      simp only [evalListHOLExact, h1, h2]
      have e1 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 bs[i0].toNat)
          (BitVec.ofNat 64 48) = decide (bs[i0].toNat = 48) := by
        by_cases h : bs[i0].toNat = 48
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h]
        · have hne : ¬ BitVec.ofNat 64 bs[i0].toNat = (48#64) :=
            fun e => h ((ofNat_inj _ 48 (by omega) (by decide)).mp e)
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h, hne]
      have e2 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 (skipDigitsL bs i0))
          (BitVec.ofNat 64 (i0 + 1)) = decide (skipDigitsL bs i0 ≠ i0 + 1) := by
        by_cases h : skipDigitsL bs i0 = i0 + 1
        · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h]
        · have hne : ¬ BitVec.ofNat 64 (skipDigitsL bs i0) = BitVec.ofNat 64 (i0 + 1) :=
            fun e => h ((ofNat_inj _ _ (by simp only [skipDigitsL]; omega) (by omega)).mp e)
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h, hne]
      rw [e1, e2]
      by_cases ha : bs[i0].toNat = 48 <;> by_cases hb' : skipDigitsL bs i0 = i0 + 1 <;>
        simp [ha, hb', bw, wordOpHOL, wordOp, valueIsWord, valueWord] <;> decide
    rw [ite_word u2 _ _ _ _ hand]
    have hgd : (bs[i0]?.getD 0) = bs[i0] := by rw [List.getElem?_eq_getElem hlt]; rfl
    by_cases hz : bs[i0].toNat = 48 ∧ skipDigitsL bs i0 ≠ i0 + 1
    · simp only [bw, hz, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        show ¬ (1 : BitVec 64) = 0 from by decide]
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u2 sI _ li2
      have hv : numEndL bs i0 = i0 := by
        simp only [numEndL, hei, ↓reduceIte, hgd]; rw [if_pos hz]
      right; refine ⟨by simp only [r1, hv], ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [r2, r3, r4, r5, r6, u2] <;> first | exact m1 | exact d1 | exact g1 | exact c1 | exact b1
    · simp only [bw, hz, ↓reduceIte, ne_eq, not_true_eq_false]
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u2 sE2 _ le2
      have hv : numEndL bs i0 = skipDigitsL bs i0 := by
        simp only [numEndL, hei, ↓reduceIte, hgd]; rw [if_neg hz]
      right; refine ⟨by simp only [r1, hv], ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [r2, r3, r4, r5, r6, u2] <;> first | exact m1 | exact d1 | exact g1 | exact c1 | exact b1

/-- **`numEnd` in Pancake is con-leche's `numEnd`**. -/
theorem numEnd_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat ≤ b.size) (hc : SkipDigitsCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetSpec t neFun (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b i).toNat) := by
  rw [numEnd_eq hp i hi]
  exact neFun_spec t A b.data.toList i.toNat hb (by simpa using hi) hc lb (by simpa using ln) li

end

end ConPanqueque.Scan
