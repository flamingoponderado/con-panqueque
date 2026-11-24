import ConPanqueque.Scan.KeyFun

/-! # `keyEnd` in Pancake: skip the key's plain bytes, then the closing quote or `0`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

/-- `c != 34 && c >= 32 && c != 92`. -/
def keyTest : ExpHOL 64 :=
  .op .and [.cmp .notEqual (vv sC) (.const 34),
    .op .and [.cmp .notLower (vv sC) (.const 32), .cmp .notEqual (vv sC) (.const 92)]]

def fSkipKey := ofString "skipKey"
def sK := ofString "k"

def SkipKeyCode {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code.lookup fSkipKey = some ([(sB, .one), (sN, .one), (sI, .one)], skFun keyTest, .one)

def keFun : ProgHOL 64 :=
  .dec sK .one (.const 0) (.dec sY .one (.const 0)
    (.seq (.call (some (some (.local, sK), none)) fSkipKey [vv sB, vv sN, vv sI])
      (.seq (bAt sY (vv sK))
        (.ite (.cmp .equal (vv sY) (.const 34)) (.return (vv sK)) (.return (.const 0))))))

section
variable {σ : Type}

theorem keyTest_ok : TestOK isKeyN keyTest := by
  intro σ u c hc h
  have f : ∀ k : Nat, k < 256 → (BitVec.ofNat 64 c = BitVec.ofNat 64 k ↔ c = k) := fun k hk =>
    ofNat_inj c k (by omega) (by omega)
  have f34 : (BitVec.ofNat 64 c = 34#64) ↔ c = 34 := f 34 (by decide)
  have f92 : (BitVec.ofNat 64 c = 92#64) ↔ c = 92 := f 92 (by decide)
  have l32 : (BitVec.ofNat 64 c < 32#64) ↔ c < 32 := ofNat_lt_iff c 32 (by omega) (by decide)
  simp only [keyTest, evalHOLExact, evalListHOLExact, vv, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h34 : c = 34 <;> by_cases h92 : c = 92 <;> by_cases h32 : c < 32 <;>
    simp [h34, h92, h32, f34, f92, l32, isKeyN, bw, wordOpHOL, wordOp, valueIsWord, valueWord] <;>
    first | decide | omega

theorem keFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (hi : i0 ≤ bs.length) (hc : SkipKeyCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    RetSpec t keFun (BitVec.ofNat 64 (keyEndL bs i0)) := by
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  have hle := skipL_le_length isKeyN bs _ i0 rfl hi
  unfold keFun
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sY (.val (.word 0)) (setVarHOLFinite sK (.val (.word 0)) t)
  have hcall := call3_ret t2 sK fSkipKey sB sN sI (skFun keyTest) (vv sB) (vv sN) (vv sI) A
    (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 i0) (BitVec.ofNat 64 (skipL isKeyN bs i0)) 0
    (by decide) (by decide) (by decide) hc (eval_vv t2 sB _ (by lk [t2]; exact lb))
    (eval_vv t2 sN _ (by lk [t2]; exact ln)) (eval_vv t2 sI _ (by lk [t2]; exact li)) (by lk [t2])
    (fun callee h1 h2 h3 => skFun_spec isKeyN keyTest keyTest_ok _ A bs i0
      (bytesAt_congr hb rfl rfl rfl) hi h1 h2 h3)
  rcases hcall with hs | ⟨u, hu, m1, d1, g1, c1, b1, lk1, lo1⟩
  · left; exact seq_stop t2 _ _ hs
  refine retSpec_seq hu ?_ m1 d1 g1 c1 b1
  have lb1 : u.locals.lookup sB = some (.val (.word A)) := by rw [lo1 sB (by decide)]; lk [t2]; exact lb
  have ln1 : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) := by
    rw [lo1 sN (by decide)]; lk [t2]; exact ln
  have ly1 : u.locals.lookup sY = some (.val (.word 0)) := by rw [lo1 sY (by decide)]; lk [t2]
  have e := bAt_spec u A bs sY (vv sK) (skipL isKeyN bs i0) (bytesAt_congr hb m1 d1 b1) (by omega) 0 ly1 lb1 ln1
    (eval_vv u sK _ lk1)
  refine retSpec_seq e ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sY (.val (.word (BitVec.ofNat 64 (byteL bs (skipL isKeyN bs i0)).toNat))) u
  have hcmp := ConsLoop.eval_cmp_of u2 .equal (vv sY) (.const 34)
    (BitVec.ofNat 64 (byteL bs (skipL isKeyN bs i0)).toNat) (BitVec.ofNat 64 34)
    (eval_vv u2 sY _ (by lk [u2])) (by simp [evalHOLExact])
  rw [bw_eq _ _ (by have := UInt8.toNat_lt (byteL bs (skipL isKeyN bs i0)); omega) (by decide)] at hcmp
  refine retSpec_ite hcmp (fun hw => ?_) (fun hw => ?_)
  · have h34 : (byteL bs (skipL isKeyN bs i0)).toNat = 34 := by
      cases hh : decide ((byteL bs (skipL isKeyN bs i0)).toNat = 34) <;> simp_all [bw]
    have hv : keyEndL bs i0 = skipL isKeyN bs i0 := by
      simp only [keyEndL]; rw [if_pos (by simpa [byteL] using h34)]
    rw [hv]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u2 sK _ (by lk [u2]; exact lk1)
    exact Or.inr ⟨r1, r2, r3, r4, r5, r6⟩
  · have h34 : ¬ (byteL bs (skipL isKeyN bs i0)).toNat = 34 := by intro h; simp [bw, h] at hw
    have hv : keyEndL bs i0 = 0 := by
      simp only [keyEndL]; rw [if_neg (by simpa [byteL] using h34)]
    rw [hv]
    right
    rw [evaluateHOLFiniteState_eq_evaluate_def u2 (.return _)]
    simp [evalHOLExact, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
      emptyLocalsHOLFinite, u2]

/-- **`keyEnd` in Pancake is con-leche's `keyEnd`**. -/
theorem keyEnd_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (j : USize) (hj : j.toNat ≤ b.size) (hc : SkipKeyCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat)))) :
    RetSpec t keFun (BitVec.ofNat 64 (ConLeche.Frontend.keyEnd b j).toNat) := by
  rw [keyEnd_eq hp _ j rfl]
  exact keFun_spec t A b.data.toList j.toNat hb (by simpa using hj) hc lb (by simpa using ln) li

end

end ConPanqueque.Scan
