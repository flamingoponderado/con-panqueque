import ConPanqueque.Scan.Hints

/-! # Quoted numbers (`natVal`) in Pancake

`qnFun` reads `"digits"` and returns the position after the closing quote.  The value is read
again from its position where it is used.  `qnFun_sound`: con-leche's `scanQuotedNat` accepts and
ends there. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend


def qnFun : ProgHOL 64 :=
  .dec sC .one (.const 0) (.dec sE2 .one (.const 0)
  (.seq (bAt sC (vv sI))
  (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 34)))
    (.seq (callTo sE2 fSkipDigits [vv sB, vv sN, .op .add [vv sI, .const 1]])
    (.ite (.cmp .equal (vv sE2) (.op .add [vv sI, .const 1])) hang
    (.seq (bAt sC (vv sE2))
    (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 34)))
      (.return (.op .add [vv sE2, .const 1])) hang))))
    hang)))

section
variable {σ : Type}

/-- **Quoted numbers in Pancake are sound for con-leche's `scanQuotedNat`**. -/
theorem qnFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : SkipDigitsCode t) (v : USize) (hv : v.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat)))) :
    RetP t qnFun (fun w => ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size ∧
      ∃ n, scanQuotedNat b v = .ok n e) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  unfold qnFun
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sC (.val (.word 0)) t)
  have e1 := bAt_spec t2 A b.data.toList sC (vv sI) v.toNat (bytesAt_congr hb rfl rfl rfl) (by omega) 0
    (by lk [t2]) (by lk [t2]; exact lb) (by lk [t2]; simpa using ln) (eval_vv t2 sI _ (by lk [t2]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t3 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) t2
  refine retP_ite (eval_eq_c t3 sC (byteL b.data.toList v.toNat).toNat 34
    (by have := UInt8.toNat_lt (byteL b.data.toList v.toNat); omega) (by decide) (by lk [t3]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq : (byteL b.data.toList v.toNat).toNat = 34 := by
    by_cases h : (byteL b.data.toList v.toNat).toNat = 34
    · exact h
    · simp [bw, h] at hw
  have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v ((hp.lt_iff v).mpr hvl)
  have hb34 : byteAt b v = 34 := byteAt_of_byteL hp v 34 (by decide) hq
  have li3 : t3.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by lk [t3, t2]; exact li
  have hadd : @evalHOLExact 64 σ _ t3.toExact (fun a => Classical.propDecidable (t3.memaddrs a))
      (.op .add [vv sI, .const 1]) = some (.val (.word (BitVec.ofNat 64 (v + 1).toNat))) := by
    rw [eval_add_c t3 sI _ _ li3, hv1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  obtain ⟨E, hEd⟩ : ∃ x, x = skipDigits b (v + 1) := ⟨_, rfl⟩
  have hEL := skipDigits_eq hp _ (v + 1) rfl
  rw [← hEd, hv1] at hEL
  have hEle : E.toNat ≤ b.size := by
    have := skipL_le_length isDigitN b.data.toList _ (v.toNat + 1) rfl (by simp; omega)
    rw [hEL]; simpa using this
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (v + 1).toNat)
    (v := BitVec.ofNat 64 E.toNat) (w0 := 0) (by decide) (by decide) (by decide) hc
    (eval_vv t3 sB _ (by lk [t3, t2]; exact lb)) (eval_vv t3 sN _ (by lk [t3, t2]; exact ln)) hadd
    (by lk [t3, t2])
    (fun callee h1 h2 h3 => by
      rw [hEd]; exact skipDigits_refines (callEntryStateHOLFinite t3 callee) A b hp
        (bytesAt_congr hb rfl rfl rfl) (v + 1) (by omega) h1 h2 h3)
    (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, le1, lo1⟩ := hs1
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1 sI (by decide)]; exact li3
  have hadd1 : @evalHOLExact 64 σ _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
      (.op .add [vv sI, .const 1]) = some (.val (.word (BitVec.ofNat 64 (v + 1).toNat))) := by
    rw [eval_add_c u1 sI _ _ li1, hv1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  have hcmp := ConsLoop.eval_cmp_of u1 .equal (vv sE2) (.op .add [vv sI, .const 1]) _ _ (eval_vv u1 sE2 _ le1) hadd1
  rw [bw_eq _ _ (usz_lt E) (usz_lt (v + 1))] at hcmp
  refine retP_ite hcmp (fun _ => retP_hang _ _) (fun hw => ?_)
  have hEv : E.toNat ≠ (v + 1).toNat := by intro h; simp [bw, h] at hw
  have e2 := bAt_spec u1 A b.data.toList sC (vv sE2) E.toNat (bytesAt_congr hb m1 d1 b1) (by omega)
    (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat)
    (by rw [lo1 sC (by decide)]; lk [t3]) (by rw [lo1 sB (by decide)]; lk [t3, t2]; exact lb)
    (by rw [lo1 sN (by decide)]; lk [t3, t2]; simpa using ln) (eval_vv u1 sE2 _ le1)
  refine retP_seq e2 ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList E.toNat).toNat))) u1
  refine retP_ite (eval_eq_c u2 sC (byteL b.data.toList E.toNat).toNat 34
    (by have := UInt8.toNat_lt (byteL b.data.toList E.toNat); omega) (by decide) (by lk [u2]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hqE : (byteL b.data.toList E.toNat).toNat = 34 := by
    by_cases h : (byteL b.data.toList E.toNat).toNat = 34
    · exact h
    · simp [bw, h] at hw
  have hEl : E.toNat < b.size := by have := lt_of_byteL hqE (by decide); simpa using this
  have hE1 : (E + 1).toNat = E.toNat + 1 := ConLeche.Frontend.usizeStep b E ((hp.lt_iff E).mpr hEl)
  have hbE : byteAt b E = 34 := byteAt_of_byteL hp E 34 (by decide) hqE
  have hret := eval_add_c u2 sE2 _ (BitVec.ofNat 64 1) (by lk [u2]; exact le1)
  have hsum : BitVec.ofNat 64 E.toNat + BitVec.ofNat 64 1 = BitVec.ofNat 64 (E + 1).toNat := by
    rw [hE1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  rw [hsum] at hret
  unfold RetP
  rw [evaluateHOLFiniteState_eq_evaluate_def u2 (.return _)]
  refine Or.inr ⟨BitVec.ofNat 64 (E + 1).toNat, ?_, ⟨E + 1, rfl, by omega, readNatAt b (v + 1) E, ?_⟩, ?_⟩
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL]
  · simp only [scanQuotedNat, bne_false_of hb34, ← hEd, beq_false_of_toNat hEv, bne_false_of hbE,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end ConPanqueque.Scan
