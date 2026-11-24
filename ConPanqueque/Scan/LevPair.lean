import ConPanqueque.Scan.Hints

/-! # Two-element number lists (`max`/`imax` levels) in Pancake

`lpFun` reads `[a, d]`: the open bracket, whitespace, a number, whitespace, a comma, whitespace, a
number, whitespace and the close bracket.  `lpFun_sound`: when it returns `e`, con-leche's
`scanNatList` gives a two-element list ending at `e`.  Lists of any other length are rejected,
as con-leche's `max`/`imax` branch rejects them. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

def lpFun : ProgHOL 64 :=
  .dec sC .one (.const 0) (.dec sE2 .one (.const 0) (.dec sHP .one (.const 0)
  (.seq (bAt sC (vv sI))
  (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 91)))
    (.seq (callTo sHP fSkipWs [vv sB, vv sN, .op .add [vv sI, .const 1]])
    (.seq (bAt sC (vv sHP))
    (.ite digitTest
      (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sHP])
      (.ite (.cmp .equal (vv sE2) (vv sHP)) hang
      (.seq (callTo sHP fSkipWs [vv sB, vv sN, vv sE2])
      (.seq (bAt sC (vv sHP))
      (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 44)))
        (.seq (callTo sHP fSkipWs [vv sB, vv sN, .op .add [vv sHP, .const 1]])
        (.seq (bAt sC (vv sHP))
        (.ite digitTest
          (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sHP])
          (.ite (.cmp .equal (vv sE2) (vv sHP)) hang
          (.seq (callTo sHP fSkipWs [vv sB, vv sN, vv sE2])
          (.seq (bAt sC (vv sHP))
          (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 93)))
            (.return (.op .add [vv sHP, .const 1])) hang)))))
          hang)))
        hang)))))
      hang)))
    hang))))

/-! ## con-leche's list loop, step by step -/

theorem byteAt_uget {b : ByteArray} {p : USize} (h : p < b.usize) :
    byteAt b p = b.uget p (usizeInBounds b p h) := by
  rw [byteAt, dif_pos h]

theorem nlLoop_ws (b : ByteArray) :
    ∀ n (i : USize) (acc : List Nat) (w : Bool), b.size - i.toNat = n →
      scanNatListLoop b i acc w = scanNatListLoop b (skipWs b i) acc w := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i acc w hn
    rw [skipWs.eq_def b i]
    by_cases h : i < b.usize
    · rw [dif_pos h]
      by_cases hw : isWs (b.uget i (usizeInBounds b i h)) = true
      · rw [if_pos hw, ← ih _ (by have := usizeInBounds b i h; have := usizeStep b i h; omega) (i + 1) acc w rfl]
        rw [scanNatListLoop.eq_def b i acc w, dif_pos h]
        simp only [hw, ↓reduceIte]
      · rw [if_neg hw]
    · rw [dif_neg h]

theorem nlLoop_digit {b : ByteArray} {p e : USize} {acc : List Nat} (h : p < b.usize) (c : UInt8)
    (hc : byteAt b p = c) (hd : isDigit c = true) (he : numEnd b p = e) (hep : e ≠ p) (hpe : p < e) :
    scanNatListLoop b p acc true = scanNatListLoop b e (readNatAt b p e :: acc) false := by
  rw [byteAt_uget h] at hc
  have hws : isWs c = false := by
    revert hd; simp only [isDigit, isWs, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨h1, h2⟩
    have h1' := UInt8.le_iff_toNat_le.mp h1
    have h2' := UInt8.le_iff_toNat_le.mp h2
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro hh <;> rw [hh] at h1' h2' <;> simp at h1' h2'
  have h93 : (c == 93) = false := by
    revert hd; simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, beq_eq_false_iff_ne]
    intro ⟨_, h2⟩ hh; rw [hh] at h2; have := UInt8.le_iff_toNat_le.mp h2; simp at this
  have h44 : (c == 44) = false := by
    revert hd; simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, beq_eq_false_iff_ne]
    intro ⟨h1, _⟩ hh; rw [hh] at h1; have := UInt8.le_iff_toNat_le.mp h1; simp at this
  rw [scanNatListLoop.eq_def b p acc true, dif_pos h, hc]
  simp only [hws, h93, h44, hd, Bool.false_eq_true, ↓reduceIte, Bool.not_true, he,
    beq_eq_false_iff_ne.mpr hep, dif_pos hpe]

theorem nlLoop_comma {b : ByteArray} {p : USize} {acc : List Nat} (h : p < b.usize)
    (hc : byteAt b p = 44) :
    scanNatListLoop b p acc false = scanNatListLoop b (p + 1) acc true := by
  rw [byteAt_uget h] at hc
  rw [scanNatListLoop.eq_def b p acc false, dif_pos h, hc]
  rfl

theorem nlLoop_close {b : ByteArray} {p : USize} {acc : List Nat} (h : p < b.usize)
    (hc : byteAt b p = 93) :
    scanNatListLoop b p acc false = .ok acc.reverse (p + 1) := by
  rw [byteAt_uget h] at hc
  rw [scanNatListLoop.eq_def b p acc false, dif_pos h, hc]
  rfl

theorem numEndL_ge (bs : List UInt8) (i : Nat) : i ≤ numEndL bs i := by
  have := skipL_ge isDigitN bs _ i rfl
  unfold numEndL skipDigitsL at *; simp only at *
  split
  · omega
  · split <;> omega

theorem lt_of_digit {bs : List UInt8} {p : Nat} (h : isDigitN (byteL bs p).toNat = true) : p < bs.length := by
  by_cases hl : p < bs.length
  · exact hl
  · simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ p), isDigitN] at h

section
variable {σ : Type}

def LpCodes (t : PanSemStateFiniteExact 64 σ) : Prop := SkipWsCode t ∧ SkipDigitsCode t ∧ NumEndCode t

theorem LpCodes.congr {t u : PanSemStateFiniteExact 64 σ} (h : LpCodes t) (hc : u.code = t.code) : LpCodes u := by
  unfold LpCodes SkipWsCode SkipDigitsCode NumEndCode at *
  rw [hc]; exact h

/-- What `lpFun` promises. -/
def LpQ (b : ByteArray) (v : USize) (w : BitVec 64) : Prop :=
  ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size ∧ ∃ a d, scanNatList b v = .ok [a, d] e

/-- A number item at the position in `sHP`: `digitTest`, then `numEnd`. -/
theorem lp_item (u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt u A b.data.toList) (hc : LpCodes u) (p : USize) (hpl : p.toNat ≤ b.size) (q : ProgHOL 64)
    (P : BitVec 64 → Prop)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (lp : u.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))))
    (lc : ∃ w, u.locals.lookup sC = some (.val (.word w)))
    (le : ∃ w, u.locals.lookup sE2 = some (.val (.word w)))
    (k : ∀ (u' : PanSemStateFiniteExact 64 σ) (e : USize), p.toNat < b.size → p.toNat < e.toNat →
      e.toNat ≤ b.size →
      isDigit (byteAt b p) = true → numEnd b p = e →
      u'.memory = u.memory → u'.memaddrs = u.memaddrs → u'.globals = u.globals → u'.code = u.code →
      u'.be = u.be → u'.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 e.toNat))) →
      (∀ y, y ≠ sE2 → y ≠ sC → u'.locals.lookup y = u.locals.lookup y) →
      (∃ w, u'.locals.lookup sC = some (.val (.word w))) → RetP u' q P) :
    RetP u (.seq (bAt sC (vv sHP)) (.ite digitTest
      (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sHP]) (.ite (.cmp .equal (vv sE2) (vv sHP)) hang q)) hang)) P := by
  have hL : b.size < 2 ^ 64 := hp.size
  obtain ⟨wc, lc⟩ := lc
  obtain ⟨we, le⟩ := le
  have e1 := bAt_spec u A b.data.toList sC (vv sHP) p.toNat hb (by omega) wc lc lb (by simpa using ln)
    (eval_vv u sHP _ lp)
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let u1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList p.toNat).toNat))) u
  refine retP_ite (digitTest_ok u1 (byteL b.data.toList p.toNat).toNat (UInt8.toNat_lt _) (by lk [u1])) (fun hw => ?_) (fun _ => retP_hang _ _)
  have hd : isDigitN (byteL b.data.toList p.toNat).toNat = true := by
    by_cases h : isDigitN (byteL b.data.toList p.toNat).toNat = true
    · exact h
    · simp [bw, h] at hw
  have hpl' : p.toNat < b.size := by have := lt_of_digit hd; simpa using this
  have hdA : isDigit (byteAt b p) = true := by
    rw [isDigit_eq, byteAt_eq hp p]; simpa [byteL] using hd
  obtain ⟨e, hed⟩ : ∃ x, x = numEnd b p := ⟨_, rfl⟩
  have heL := numEnd_eq hp p hpl
  rw [← hed] at heL
  have hele : e.toNat ≤ b.size := by
    have := numEndL_le b.data.toList p.toNat (by simpa using hpl)
    rw [heL]; simpa using this
  have hpe : p.toNat ≤ e.toNat := by rw [heL]; exact numEndL_ge _ _
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 p.toNat)
    (v := BitVec.ofNat 64 e.toNat) (w0 := we) (by decide) (by decide) (by decide) hc.2.2
    (eval_vv u1 sB _ (by lk [u1]; exact lb)) (eval_vv u1 sN _ (by lk [u1]; exact ln))
    (eval_vv u1 sHP _ (by lk [u1]; exact lp)) (by lk [u1]; exact le)
    (fun callee h1 h2 h3 => by
      rw [hed]; exact numEnd_refines (callEntryStateHOLFinite u1 callee) A b hp
        (bytesAt_congr hb rfl rfl rfl) p hpl hc.2.1 h1 h2 h3)
    (fun u2 hs2 => ?_)
  obtain ⟨m2, d2, g2, c2, b2, le2, lo2⟩ := hs2
  have lp2 : u2.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))) := by
    rw [lo2 sHP (by decide)]; lk [u1]; exact lp
  have hcmp := ConsLoop.eval_cmp_of u2 .equal (vv sE2) (vv sHP) _ _ (eval_vv u2 sE2 _ le2) (eval_vv u2 sHP _ lp2)
  rw [bw_eq _ _ (usz_lt e) (usz_lt p)] at hcmp
  refine retP_ite hcmp (fun _ => retP_hang _ _) (fun hw => ?_)
  have hep : e.toNat ≠ p.toNat := by intro h; simp [bw, h] at hw
  exact k u2 e hpl' (by omega) hele hdA hed.symm m2 d2 g2 c2 b2 le2
    (fun y h1 h2 => by rw [lo2 y h1]; show (setVarHOLFinite _ _ u).locals.lookup y = _
                       rw [lookup_setVar_other _ _ h2])
    ⟨_, by rw [lo2 sC (by decide)]; lk [u1] <;> rfl⟩

/-- Whitespace then one expected byte at the position in `sHP`. -/
theorem lp_ws_byte (u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt u A b.data.toList) (hc : LpCodes u) (x : ExpHOL 64) (i : USize) (hi : i.toNat ≤ b.size)
    (c : Nat) (hc256 : c < 256) (hc0 : c ≠ 0) (q : ProgHOL 64) (P : BitVec 64 → Prop)
    (hx : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) x =
      some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (lp : ∃ w, u.locals.lookup sHP = some (.val (.word w)))
    (lc : ∃ w, u.locals.lookup sC = some (.val (.word w)))
    (k : ∀ (u' : PanSemStateFiniteExact 64 σ), (skipWs b i).toNat < b.size → byteAt b (skipWs b i) = UInt8.ofNat c →
      u'.memory = u.memory → u'.memaddrs = u.memaddrs → u'.globals = u.globals → u'.code = u.code →
      u'.be = u.be →
      u'.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 (skipWs b i).toNat))) →
      (∀ y, y ≠ sHP → y ≠ sC → u'.locals.lookup y = u.locals.lookup y) →
      (∃ w, u'.locals.lookup sC = some (.val (.word w))) → RetP u' q P) :
    RetP u (.seq (callTo sHP fSkipWs [vv sB, vv sN, x]) (.seq (bAt sC (vv sHP))
      (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 c))) q hang))) P := by
  have hL : b.size < 2 ^ 64 := hp.size
  obtain ⟨wp, lp⟩ := lp
  obtain ⟨wc, lc⟩ := lc
  obtain ⟨s, hsd⟩ : ∃ x, x = skipWs b i := ⟨_, rfl⟩
  have hsL := skipWs_eq hp _ i rfl
  rw [← hsd] at hsL
  have hsle : s.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ i.toNat rfl (by simpa using hi)
    rw [hsL]; simpa using this
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 i.toNat)
    (v := BitVec.ofNat 64 s.toNat) (w0 := wp) (by decide) (by decide) (by decide) hc.1
    (eval_vv u sB _ lb) (eval_vv u sN _ ln) hx lp
    (fun callee h1 h2 h3 => by
      rw [hsd]; exact skipWs_refines (callEntryStateHOLFinite u callee) A b hp
        (bytesAt_congr hb rfl rfl rfl) i hi h1 h2 h3)
    (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, lp1, lo1⟩ := hs1
  have e2 := bAt_spec u1 A b.data.toList sC (vv sHP) s.toNat (bytesAt_congr hb m1 d1 b1) (by omega) wc
    (by rw [lo1 sC (by decide)]; exact lc) (by rw [lo1 sB (by decide)]; exact lb)
    (by rw [lo1 sN (by decide)]; simpa using ln) (eval_vv u1 sHP _ lp1)
  refine retP_seq e2 ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList s.toNat).toNat))) u1
  refine retP_ite (eval_eq_c u2 sC (byteL b.data.toList s.toNat).toNat c
    (by have := UInt8.toNat_lt (byteL b.data.toList s.toNat); omega) (by omega) (by lk [u2]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq : (byteL b.data.toList s.toNat).toNat = c := by
    by_cases h : (byteL b.data.toList s.toNat).toNat = c
    · exact h
    · simp [bw, h] at hw
  have hsl : s.toNat < b.size := by have := lt_of_byteL hq hc0; simpa using this
  have hbs := byteAt_of_byteL hp s c hc256 hq
  subst hsd
  have hm := k u2 hsl hbs m1 d1 g1 c1 b1 (by lk [u2]; exact lp1)
    (fun y h1 h2 => by
      show (setVarHOLFinite _ _ u1).locals.lookup y = _
      rw [lookup_setVar_other _ _ h2, lo1 y h1]) ⟨_, by lk [u2] <;> rfl⟩
  exact hm

/-- **A two-element number list in Pancake is sound for con-leche's `scanNatList`**. -/
theorem lpFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : LpCodes t) (v : USize) (hv : v.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat)))) :
    RetP t lpFun (LpQ b v) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  unfold lpFun
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sHP (.val (.word 0)) (setVarHOLFinite sE2 (.val (.word 0))
    (setVarHOLFinite sC (.val (.word 0)) t))
  have e1 := bAt_spec t2 A b.data.toList sC (vv sI) v.toNat (bytesAt_congr hb rfl rfl rfl) (by omega) 0
    (by lk [t2]) (by lk [t2]; exact lb) (by lk [t2]; simpa using ln) (eval_vv t2 sI _ (by lk [t2]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t3 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) t2
  refine retP_ite (eval_eq_c t3 sC (byteL b.data.toList v.toNat).toNat 91
    (by have := UInt8.toNat_lt (byteL b.data.toList v.toNat); omega) (by decide) (by lk [t3]))
    (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq : (byteL b.data.toList v.toNat).toNat = 91 := by
    by_cases h : (byteL b.data.toList v.toNat).toNat = 91
    · exact h
    · simp [bw, h] at hw
  have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v ((hp.lt_iff v).mpr hvl)
  have hb91 : byteAt b v = 91 := byteAt_of_byteL hp v 91 (by decide) hq
  have lb3 : t3.locals.lookup sB = some (.val (.word A)) := by lk [t3, t2]; exact lb
  have ln3 : t3.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by lk [t3, t2]; exact ln
  -- p1: whitespace, then the first number
  obtain ⟨p1, hp1d⟩ : ∃ x, x = skipWs b (v + 1) := ⟨_, rfl⟩
  have hp1L := skipWs_eq hp _ (v + 1) rfl
  rw [← hp1d, hv1] at hp1L
  have hp1le : p1.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ (v.toNat + 1) rfl (by simp; omega)
    rw [hp1L]; simpa using this
  obtain ⟨wp, lp3⟩ : ∃ w, t3.locals.lookup sHP = some (.val (.word w)) := ⟨_, by lk [t3, t2] <;> rfl⟩
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (v + 1).toNat)
    (v := BitVec.ofNat 64 p1.toNat) (w0 := wp) (by decide) (by decide) (by decide) hc.1
    (eval_vv t3 sB _ lb3) (eval_vv t3 sN _ ln3)
    (by rw [eval_add_c t3 sI _ _ (by lk [t3, t2]; exact li), hv1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) lp3
    (fun callee h1 h2 h3 => by
      rw [hp1d]; exact skipWs_refines (callEntryStateHOLFinite t3 callee) A b hp
        (bytesAt_congr hb rfl rfl rfl) (v + 1) (by omega) h1 h2 h3)
    (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, lp1, lo1⟩ := hs1
  refine lp_item u1 A b hp (bytesAt_congr hb m1 d1 b1) (hc.congr c1) p1 hp1le _ _
    (by rw [lo1 sB (by decide)]; exact lb3) (by rw [lo1 sN (by decide)]; exact ln3) lp1
    ⟨_, by rw [lo1 sC (by decide)]; lk [t3] <;> rfl⟩ ⟨_, by rw [lo1 sE2 (by decide)]; lk [t3, t2] <;> rfl⟩ ?_
  intro u2 e1 hp1l hp1e he1le hd1 he1d m2 d2 g2 c2 b2 le2 lo2 lc2
  -- q1: whitespace, then the comma
  refine lp_ws_byte u2 A b hp (bytesAt_congr hb (m2.trans m1) (d2.trans d1) (b2.trans b1))
    ((hc.congr c1).congr c2) (vv sE2) e1 he1le 44 (by decide) (by decide) _ _ (eval_vv u2 sE2 _ le2)
    (by rw [lo2 sB (by decide) (by decide), lo1 sB (by decide)]; exact lb3)
    (by rw [lo2 sN (by decide) (by decide), lo1 sN (by decide)]; exact ln3)
    ⟨_, by rw [lo2 sHP (by decide) (by decide)]; exact lp1⟩ lc2 ?_
  intro u3 hq1l hq1b m3 d3 g3 c3 b3 lp3' lo3 lc3
  have hq11 : (skipWs b e1 + 1).toNat = (skipWs b e1).toNat + 1 :=
    ConLeche.Frontend.usizeStep b _ ((hp.lt_iff _).mpr hq1l)
  -- p2: whitespace, then the second number
  obtain ⟨p2, hp2d⟩ : ∃ x, x = skipWs b (skipWs b e1 + 1) := ⟨_, rfl⟩
  have hp2L := skipWs_eq hp _ (skipWs b e1 + 1) rfl
  rw [← hp2d, hq11] at hp2L
  have hp2le : p2.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ ((skipWs b e1).toNat + 1) rfl (by simp; omega)
    rw [hp2L]; simpa using this
  have lb3' : u3.locals.lookup sB = some (.val (.word A)) := by
    rw [lo3 sB (by decide) (by decide), lo2 sB (by decide) (by decide), lo1 sB (by decide)]; exact lb3
  have ln3' : u3.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    rw [lo3 sN (by decide) (by decide), lo2 sN (by decide) (by decide), lo1 sN (by decide)]; exact ln3
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (skipWs b e1 + 1).toNat)
    (v := BitVec.ofNat 64 p2.toNat) (w0 := BitVec.ofNat 64 (skipWs b e1).toNat) (by decide) (by decide) (by decide)
    (((hc.congr c1).congr c2).congr c3).1
    (eval_vv u3 sB _ lb3') (eval_vv u3 sN _ ln3')
    (by rw [eval_add_c u3 sHP _ _ lp3', hq11]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) lp3'
    (fun callee h1 h2 h3 => by
      rw [hp2d]; exact skipWs_refines (callEntryStateHOLFinite u3 callee) A b hp
        (bytesAt_congr hb (m3.trans (m2.trans m1)) (d3.trans (d2.trans d1)) (b3.trans (b2.trans b1)))
        _ (by omega) h1 h2 h3)
    (fun u4 hs4 => ?_)
  obtain ⟨m4, d4, g4, c4, b4, lp4, lo4⟩ := hs4
  obtain ⟨wc3, lc3'⟩ := lc3
  refine lp_item u4 A b hp
    (bytesAt_congr hb (m4.trans (m3.trans (m2.trans m1))) (d4.trans (d3.trans (d2.trans d1)))
      (b4.trans (b3.trans (b2.trans b1))))
    ((((hc.congr c1).congr c2).congr c3).congr c4) p2 hp2le _ _
    (by rw [lo4 sB (by decide)]; exact lb3') (by rw [lo4 sN (by decide)]; exact ln3') lp4
    ⟨_, by rw [lo4 sC (by decide)]; exact lc3'⟩
    ⟨_, by rw [lo4 sE2 (by decide), lo3 sE2 (by decide) (by decide)]; exact le2⟩ ?_
  intro u5 e2 hp2l hp2e he2le hd2 he2d m5 d5 g5 c5 b5 le5 lo5 lc5
  -- q2: whitespace, then the close bracket
  refine lp_ws_byte u5 A b hp
    (bytesAt_congr hb (m5.trans (m4.trans (m3.trans (m2.trans m1))))
      (d5.trans (d4.trans (d3.trans (d2.trans d1)))) (b5.trans (b4.trans (b3.trans (b2.trans b1)))))
    (((((hc.congr c1).congr c2).congr c3).congr c4).congr c5) (vv sE2) e2 he2le 93 (by decide) (by decide) _ _
    (eval_vv u5 sE2 _ le5)
    (by rw [lo5 sB (by decide) (by decide), lo4 sB (by decide)]; exact lb3')
    (by rw [lo5 sN (by decide) (by decide), lo4 sN (by decide)]; exact ln3')
    ⟨_, by rw [lo5 sHP (by decide) (by decide)]; exact lp4⟩ lc5 ?_
  intro u6 hq2l hq2b m6 d6 g6 c6 b6 lp6 lo6 lc6
  have hq21 : (skipWs b e2 + 1).toNat = (skipWs b e2).toNat + 1 :=
    ConLeche.Frontend.usizeStep b _ ((hp.lt_iff _).mpr hq2l)
  have hret := eval_add_c u6 sHP _ (BitVec.ofNat 64 1) lp6
  have hsum : BitVec.ofNat 64 (skipWs b e2).toNat + BitVec.ofNat 64 1 = BitVec.ofNat 64 (skipWs b e2 + 1).toNat := by
    rw [hq21]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  rw [hsum] at hret
  unfold RetP
  rw [evaluateHOLFiniteState_eq_evaluate_def u6 (.return _)]
  refine Or.inr ⟨BitVec.ofNat 64 (skipWs b e2 + 1).toNat, ?_, ⟨skipWs b e2 + 1, rfl, by omega,
    readNatAt b p1 e1, readNatAt b p2 e2, ?_⟩, ?_⟩
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL]
  · have hb91' : (byteAt b v == 91) = true := by rw [hb91]; rfl
    rw [scanNatList, if_pos hb91', nlLoop_ws b _ _ _ _ rfl, ← hp1d,
      nlLoop_digit ((hp.lt_iff p1).mpr hp1l) _ rfl hd1 he1d (fun h => by rw [h] at hp1e; omega)
        (USize.lt_iff_toNat_lt.mpr hp1e),
      nlLoop_ws b _ e1 _ _ rfl, nlLoop_comma ((hp.lt_iff _).mpr hq1l) hq1b,
      nlLoop_ws b _ _ _ _ rfl, ← hp2d,
      nlLoop_digit ((hp.lt_iff p2).mpr hp2l) _ rfl hd2 he2d (fun h => by rw [h] at hp2e; omega)
        (USize.lt_iff_toNat_lt.mpr hp2e),
      nlLoop_ws b _ e2 _ _ rfl, nlLoop_close ((hp.lt_iff _).mpr hq2l) hq2b]
    rfl
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end ConPanqueque.Scan
