import ConPanqueque.Scan.KeyEnd

/-! # `valueAt` in Pancake: whitespace, the colon, whitespace. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def fSkipWs := ofString "skipWs"

def SkipWsCode {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code.lookup fSkipWs = some ([(sB, .one), (sN, .one), (sI, .one)], skFun wsTest, .one)

/-- `valueAt(b, n, i, k)` with `k` the key's closing quote. -/
def vaFun : ProgHOL 64 :=
  .dec sY .one (.const 0) (.dec sE2 .one (.const 0)
    (.seq (.call (some (some (.local, sE2), none)) fSkipWs [vv sB, vv sN, .op .add [vv sK, .const 1]])
      (.seq (bAt sY (vv sE2))
        (.ite (.cmp .equal (vv sY) (.const 58))
          (.seq (.call (some (some (.local, sE2), none)) fSkipWs [vv sB, vv sN, .op .add [vv sE2, .const 1]])
            (.return (vv sE2)))
          (.return (vv sI))))))

section
variable {σ : Type}

theorem vaFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 ke : Nat)
    (hb : BytesAt t A bs) (hke : ke < bs.length) (hi0 : i0 < 2 ^ 64) (hc : SkipWsCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0))))
    (lk0 : t.locals.lookup sK = some (.val (.word (BitVec.ofNat 64 ke)))) :
    RetSpec t vaFun (BitVec.ofNat 64 (valueAtL bs i0 ke)) := by
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  unfold vaFun
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sY (.val (.word 0)) t)
  have hle := skipL_le_length isWsN bs _ (ke + 1) rfl (by omega)
  have hcall := call3_ret t2 sE2 fSkipWs sB sN sI (skFun wsTest) (vv sB) (vv sN) (.op .add [vv sK, .const 1]) A
    (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 (ke + 1)) (BitVec.ofNat 64 (skipWsL bs (ke + 1))) 0
    (by decide) (by decide) (by decide) hc (eval_vv t2 sB _ (by lk [t2]; exact lb))
    (eval_vv t2 sN _ (by lk [t2]; exact ln))
    (by rw [eval_add_c t2 sK _ _ (by lk [t2]; exact lk0)]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) (by lk [t2])
    (fun callee h1 h2 h3 => skFun_spec isWsN wsTest wsTest_ok _ A bs (ke + 1)
      (bytesAt_congr hb rfl rfl rfl) (by omega) h1 h2 h3)
  rcases hcall with hs | ⟨u, hu, m1, d1, g1, c1, b1, le1, lo1⟩
  · left; exact seq_stop t2 _ _ hs
  refine retSpec_seq hu ?_ m1 d1 g1 c1 b1
  have lb1 : u.locals.lookup sB = some (.val (.word A)) := by rw [lo1 sB (by decide)]; lk [t2]; exact lb
  have ln1 : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) := by
    rw [lo1 sN (by decide)]; lk [t2]; exact ln
  have ly1 : u.locals.lookup sY = some (.val (.word 0)) := by rw [lo1 sY (by decide)]; lk [t2]
  have li1 : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0))) := by
    rw [lo1 sI (by decide)]; lk [t2]; exact li
  obtain ⟨P, hP⟩ : ∃ P, P = skipWsL bs (ke + 1) := ⟨_, rfl⟩
  rw [← hP] at le1
  have hle' : P ≤ bs.length := by rw [hP]; exact hle
  have e := bAt_spec u A bs sY (vv sE2) P (bytesAt_congr hb m1 d1 b1) (by omega) 0 ly1 lb1 ln1 (eval_vv u sE2 _ le1)
  refine retSpec_seq e ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sY (.val (.word (BitVec.ofNat 64 (byteL bs P).toNat))) u
  have hcmp := ConsLoop.eval_cmp_of u2 .equal (vv sY) (.const 58) (BitVec.ofNat 64 (byteL bs P).toNat)
    (BitVec.ofNat 64 58) (eval_vv u2 sY _ (by lk [u2])) (by simp [evalHOLExact])
  rw [bw_eq _ _ (by have := UInt8.toNat_lt (byteL bs P); omega) (by decide)] at hcmp
  refine retSpec_ite hcmp (fun hw => ?_) (fun hw => ?_)
  · have h58 : (byteL bs P).toNat = 58 := by
      cases hh : decide ((byteL bs P).toNat = 58) <;> simp_all [bw]
    have hPl : P < bs.length := by
      by_cases h : P < bs.length
      · exact h
      · simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ P)] at h58
    have hle2 := skipL_le_length isWsN bs _ (P + 1) rfl (by omega)
    have hv : valueAtL bs i0 ke = skipWsL bs (P + 1) := by
      simp only [valueAtL, ← hP]; rw [ite_eq_left (by simpa [byteL] using h58)]
    rw [hv]
    have hcall := call3_ret u2 sE2 fSkipWs sB sN sI (skFun wsTest) (vv sB) (vv sN) (.op .add [vv sE2, .const 1])
      A (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 (P + 1)) (BitVec.ofNat 64 (skipWsL bs (P + 1)))
      (BitVec.ofNat 64 P) (by decide) (by decide) (by decide) (by rw [show u2.code = t.code from c1]; exact hc)
      (eval_vv u2 sB _ (by lk [u2]; exact lb1)) (eval_vv u2 sN _ (by lk [u2]; exact ln1))
      (by rw [eval_add_c u2 sE2 _ _ (by lk [u2]; exact le1)]; congr 3; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]; try omega) (by lk [u2]; exact le1)
      (fun callee h1 h2 h3 => skFun_spec isWsN wsTest wsTest_ok _ A bs (P + 1)
        (bytesAt_congr hb (by exact m1) (by exact d1) (by exact b1)) (by omega) h1 h2 h3)
    rcases hcall with hs | ⟨u3, hu3, m3, d3, g3, c3, b3, le3, -⟩
    · left; exact seq_stop u2 _ _ hs
    refine retSpec_seq hu3 ?_ m3 d3 g3 c3 b3
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u3 sE2 _ le3
    exact Or.inr ⟨r1, r2, r3, r4, r5, r6⟩
  · have h58 : ¬ (byteL bs P).toNat = 58 := by intro h; simp [bw, h] at hw
    have hv : valueAtL bs i0 ke = i0 := by
      simp only [valueAtL, ← hP]; rw [ite_eq_right (by simpa [byteL] using h58)]
    rw [hv]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := return_vv u2 sI _ (by lk [u2]; exact li1)
    exact Or.inr ⟨r1, r2, r3, r4, r5, r6⟩

/-- **`valueAt` in Pancake is con-leche's `valueAt`**, at a key's closing quote `ke`. -/
theorem valueAt_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i ke : USize) (hke : ke.toNat < b.size) (hc : SkipWsCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lk0 : t.locals.lookup sK = some (.val (.word (BitVec.ofNat 64 ke.toNat)))) :
    RetSpec t vaFun (BitVec.ofNat 64 (ConLeche.Frontend.valueAt b i ke).toNat) := by
  rw [valueAt_eq hp i ke hke]
  have hi : i.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_two_pow_numBits i)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega))
  exact vaFun_spec t A b.data.toList i.toNat ke.toNat hb (by simpa using hke) hi hc lb (by simpa using ln) li lk0

end

end ConPanqueque.Scan
