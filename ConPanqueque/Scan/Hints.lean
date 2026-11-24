import ConPanqueque.Scan.ObjBase

/-! # `scanHints` in Pancake

A definition's `hints` value: `"abbrev"`, `"opaque"` (a literal choice from the byte after the
quote) or `{"regular":n}` (one key, then a number, then the closing brace).  `hiFun` returns the
position after the value; the value itself is read again from its position where it is used.
`hiFun_sound`: when it returns `e`, con-leche's `scanHints` accepts and ends at `e`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

def sHP := ofString "hpos"
def fHints := ofString "scanHints"

/-- `abbrev"` and `opaque"`, after the opening quote. -/
def hintCands : List (List UInt8 × Nat) :=
  [([97, 98, 98, 114, 101, 118, 34], 7), ([111, 112, 97, 113, 117, 101, 34], 7)]

def hqBody : ProgHOL 64 :=
  .dec sJ .one (.op .add [vv sI, .const 1]) (.dec sL .one (.const 0) (.dec sX .one (.const 0)
    (.dec sY .one (.const 0) (.dec sOk .one (.const 0) (genChoice hang hintCands)))))

def hrBody : ProgHOL 64 :=
  .seq (callTo sHP fSkipWs [vv sB, vv sN, .op .add [vv sI, .const 1]])
  (.seq (bAt sC (vv sHP))
  (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 34)))
    (.seq (callTo sK fKeyEnd [vv sB, vv sN, .op .add [vv sHP, .const 1]])
    (.ite (.cmp .equal (vv sK) (.const (BitVec.ofNat 64 0))) hang
    (.seq (callTo sKK fKeyAt [vv sB, vv sN, vv sHP, .op .sub [vv sK, .op .add [vv sHP, .const 1]]])
    (.ite (.cmp .equal (vv sKK) (.const (BitVec.ofNat 64 Key.kRegular.ctorIdx)))
      (.seq (callTo sV fValueAt [vv sB, vv sN, vv sHP, vv sK])
      (.ite (.cmp .equal (vv sV) (vv sHP)) hang
      (.seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sV])
      (.ite (.cmp .equal (vv sE2) (vv sV)) hang
      (.seq (callTo sHP fSkipWs [vv sB, vv sN, vv sE2])
      (.seq (bAt sC (vv sHP))
      (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 125)))
        (.return (.op .add [vv sHP, .const 1])) hang)))))))
      hang))))
    hang))

/-- `scanHints(b, n, i)`: the position after the hints value at `i`; anything else is rejected. -/
def hiFun : ProgHOL 64 :=
  .dec sC .one (.const 0) (.dec sE2 .one (.const 0) (.dec sK .one (.const 0) (.dec sV .one (.const 0)
    (.dec sKK .one (.const 0) (.dec sHP .one (.const 0)
      (.seq (bAt sC (vv sI))
        (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 34))) hqBody
          (.ite (.cmp .equal (vv sC) (.const (BitVec.ofNat 64 123))) hrBody hang))))))))

theorem litsL_get (bs : List UInt8) (j : Nat) :
    ∀ (cs : List UInt8) (k : Nat), litsL bs j cs k = true → ∀ m (hm : m < cs.length), byteL bs (j + k + m) = cs[m] := by
  intro cs
  induction cs with
  | nil => intro k _ m hm; simp at hm
  | cons c cs ih =>
    intro k h m hm
    simp only [litsL, Bool.and_eq_true, beq_iff_eq] at h
    cases m with
    | zero => simpa using h.1
    | succ m =>
      have := ih (k + 1) h.2 m (by simpa using hm)
      rw [show j + k + (m + 1) = j + (k + 1) + m by omega]; simpa using this

section
variable {σ : Type}

/-- The callees `hiFun` uses. -/
def HintCodes (t : PanSemStateFiniteExact 64 σ) : Prop :=
  SkipWsCode t ∧ SkipDigitsCode t ∧ SkipKeyCode t ∧ NumEndCode t ∧
  t.code.lookup fKeyEnd = some ([(sB, .one), (sN, .one), (sI, .one)], keFun, .one) ∧
  t.code.lookup fValueAt = some ([(sB, .one), (sN, .one), (sI, .one), (sK, .one)], vaFun, .one) ∧
  t.code.lookup fKeyAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], kaFun, .one)

theorem HintCodes.congr {t u : PanSemStateFiniteExact 64 σ} (h : HintCodes t) (hc : u.code = t.code) :
    HintCodes u := by
  unfold HintCodes SkipWsCode SkipDigitsCode SkipKeyCode NumEndCode at *
  rw [hc]; exact h

theorem retP_call3 {s : PanSemStateFiniteExact 64 σ} {x f x1 x2 x3 : MlS} {body q : ProgHOL 64}
    {a1 a2 a3 : ExpHOL 64} {v1 v2 v3 v w0 : BitVec 64} {P : BitVec 64 → Prop}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetSpec (callEntryStateHOLFinite s callee) body v)
    (k : ∀ u, SetsLocal s x v u → RetP u q P) : RetP s (.seq (callTo x f [a1, a2, a3]) q) P := by
  rcases call3_ret s x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 v w0 h12 h13 h23 hcode ha1 ha2 ha3 hx hbody with
    hs | ⟨u, hu, m, d, g, c, b, lx, lo⟩
  · exact Or.inl (seq_stop s _ _ hs)
  · exact retP_seq hu (k u ⟨m, d, g, c, b, lx, lo⟩) m d g c b

theorem retP_call4 {s : PanSemStateFiniteExact 64 σ} {x f x1 x2 x3 x4 : MlS} {body q : ProgHOL 64}
    {a1 a2 a3 a4 : ExpHOL 64} {v1 v2 v3 v4 v w0 : BitVec 64} {P : BitVec 64 → Prop}
    (hnd : [x1, x2, x3, x4].Nodup)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one), (x4, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (ha4 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a4 =
      some (.val (.word v4)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → callee.lookup x4 = some (.val (.word v4)) →
      RetSpec (callEntryStateHOLFinite s callee) body v)
    (k : ∀ u, SetsLocal s x v u → RetP u q P) : RetP s (.seq (callTo x f [a1, a2, a3, a4]) q) P := by
  rcases call4_ret s x f x1 x2 x3 x4 body a1 a2 a3 a4 v1 v2 v3 v4 v w0 hnd hcode ha1 ha2 ha3 ha4 hx hbody with
    hs | ⟨u, hu, m, d, g, c, b, lx, lo⟩
  · exact Or.inl (seq_stop s _ _ hs)
  · exact retP_seq hu (k u ⟨m, d, g, c, b, lx, lo⟩) m d g c b

theorem ofNat_add64 (a k : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a + k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

/-- What `hiFun` promises. -/
def HintQ (b : ByteArray) (v : USize) (w : BitVec 64) : Prop :=
  ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size ∧ ∃ x, scanHints b v = .ok x e

theorem byteAt_of_byteL {b : ByteArray} (hp : Plat b) (p : USize) (c : Nat) (hc : c < 256)
    (h : (byteL b.data.toList p.toNat).toNat = c) : byteAt b p = UInt8.ofNat c := by
  rw [byteAt_eq hp p]; apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; simpa [byteL] using h

theorem lt_of_byteL {bs : List UInt8} {p c : Nat} (h : (byteL bs p).toNat = c) (hc : c ≠ 0) : p < bs.length := by
  by_cases hl : p < bs.length
  · exact hl
  · simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ p)] at h; omega

/-- The quoted branch: `"abbrev"` or `"opaque"`. -/
theorem hq_sound (u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt u A b.data.toList) (v : USize) (hvl : v.toNat < b.size) (hbyte : byteAt b v = 34)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat)))) :
    RetP u hqBody (HintQ b v) := by
  have hroom := hp.room
  have hvu : v < b.usize := (hp.lt_iff v).mpr hvl
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v hvu
  unfold hqBody
  refine retP_dec (w := BitVec.ofNat 64 (v.toNat + 1)) (by rw [eval_add_c u sI _ _ li, ← ofNat_add64]; rfl) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine genChoice_spec _ A b.data.toList (v.toNat + 1) 0 (bytesAt_congr hb rfl rfl rfl) (by omega) hang _ hintCands _
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, by lk; exact lb, by lk; simpa using ln, by lk, by lk; rfl, ⟨0, by lk⟩,
      ⟨0, by lk⟩, ⟨0, by lk⟩⟩ (fun off h => ?_) (fun _ u' _ => retP_hang u' _)
  have ma := matchLit_L hp "abbrev\"".toUTF8 (by decide) (by decide) _ (v + 1) 0 rfl
    (by have : "abbrev\"".toUTF8.size = 7 := by decide
        rw [this, hv1]; simp only [USize.toNat_zero]; omega) (by simp)
  have mo := matchLit_L hp "opaque\"".toUTF8 (by decide) (by decide) _ (v + 1) 0 rfl
    (by have : "opaque\"".toUTF8.size = 7 := by decide
        rw [this, hv1]; simp only [USize.toNat_zero]; omega) (by simp)
  have da : "abbrev\"".toUTF8.data.toList = [97, 98, 98, 114, 101, 118, 34] := by decide
  have dq : "opaque\"".toUTF8.data.toList = [111, 112, 97, 113, 117, 101, 34] := by decide
  simp only [da, dq, List.drop_zero, USize.toNat_zero, hv1] at ma mo
  have h8 : (v + 8).toNat = v.toNat + 8 := usize_add_toNat hp.bits v 8 (by omega)
  have hb34 : (byteAt b v == 34) = true := by rw [hbyte]; rfl
  simp only [choiceL, hintCands] at h
  split at h
  · rename_i ha
    simp only [Option.some.injEq] at h; subst h
    have := litsL_get _ _ _ 0 ha 6 (by decide)
    have hl := lt_of_byteL (c := 34) (by rw [this]; rfl) (by decide)
    refine ⟨v + 8, by rw [h8], by rw [h8]; simp at hl; omega, .«abbrev», ?_⟩
    rw [scanHints, if_pos hb34, ma, if_pos ha]
  · rename_i ha
    split at h
    · rename_i ho
      simp only [Option.some.injEq] at h; subst h
      have := litsL_get _ _ _ 0 ho 6 (by decide)
      have hl := lt_of_byteL (c := 34) (by rw [this]; rfl) (by decide)
      refine ⟨v + 8, by rw [h8], by rw [h8]; simp at hl; omega, .«opaque», ?_⟩
      rw [scanHints, if_pos hb34, ma, if_neg ha, mo, if_pos ho]
    · simp at h


theorem bne_false_of {a c : UInt8} (h : a = c) : (a != c) = false := by rw [h]; simp

theorem beq_false_of_toNat {a c : USize} (h : a.toNat ≠ c.toNat) : (a == c) = false :=
  beq_eq_false_iff_ne.mpr (fun h' => h (by rw [h']))

/-- The object branch: `{"regular": n}`. -/
theorem hr_sound (u0 : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt u0 A b.data.toList) (hc : HintCodes u0) (v : USize) (hvl : v.toNat < b.size)
    (hbyte : byteAt b v = 123)
    (lb : u0.locals.lookup sB = some (.val (.word A)))
    (ln : u0.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u0.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))))
    (lsc : ∀ x ∈ [sC, sE2, sK, sV, sKK, sHP], ∃ w, u0.locals.lookup x = some (.val (.word w))) :
    RetP u0 hrBody (HintQ b v) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvu : v < b.usize := (hp.lt_iff v).mpr hvl
  have hv1 : (v + 1).toNat = v.toNat + 1 := ConLeche.Frontend.usizeStep b v hvu
  obtain ⟨wC, lC⟩ := lsc sC (by simp)
  obtain ⟨wK, lK⟩ := lsc sK (by simp)
  obtain ⟨wV, lV⟩ := lsc sV (by simp)
  obtain ⟨wE, lE⟩ := lsc sE2 (by simp)
  obtain ⟨wKK, lKK⟩ := lsc sKK (by simp)
  obtain ⟨wP, lP⟩ := lsc sHP (by simp)
  unfold hrBody
  -- p := skipWs b (v + 1)
  obtain ⟨p, hpd⟩ : ∃ p, p = skipWs b (v + 1) := ⟨_, rfl⟩
  have hpL := skipWs_eq hp _ (v + 1) rfl
  rw [← hpd, hv1] at hpL
  have hple : p.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ (v.toNat + 1) rfl (by simp; omega)
    rw [hpL]; simpa using this
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (v + 1).toNat)
    (v := BitVec.ofNat 64 p.toNat) (w0 := wP) (by decide) (by decide) (by decide) hc.1
    (eval_vv u0 sB _ lb) (eval_vv u0 sN _ ln)
    (by rw [eval_add_c u0 sI _ _ li, hv1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
    lP (fun callee h1 h2 h3 => by
      rw [hpd]; exact skipWs_refines (callEntryStateHOLFinite u0 callee) A b hp
        (bytesAt_congr hb rfl rfl rfl) (v + 1) (by omega) h1 h2 h3) (fun u1 hs1 => ?_)
  obtain ⟨m1, d1, g1, c1, b1, lp1, lo1⟩ := hs1
  have hc1 : HintCodes u1 := hc.congr c1
  have e2 := bAt_spec u1 A b.data.toList sC (vv sHP) p.toNat (bytesAt_congr hb m1 d1 b1) (by omega) wC
    (by rw [lo1 sC (by decide)]; exact lC) (by rw [lo1 sB (by decide)]; exact lb)
    (by rw [lo1 sN (by decide)]; simpa using ln) (eval_vv u1 sHP _ lp1)
  refine retP_seq e2 ?_ rfl rfl rfl rfl rfl
  let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList p.toNat).toNat))) u1
  refine retP_ite (eval_eq_c u2 sC (byteL b.data.toList p.toNat).toNat 34 (by have := UInt8.toNat_lt (byteL b.data.toList p.toNat); omega)
    (by decide) (by lk [u2])) (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq34 : (byteL b.data.toList p.toNat).toNat = 34 := by
    by_cases h : (byteL b.data.toList p.toNat).toNat = 34
    · exact h
    · simp [bw, h] at hw
  have hpl : p.toNat < b.size := by have := lt_of_byteL hq34 (by decide); simpa using this
  have hp1 : (p + 1).toNat = p.toNat + 1 := ConLeche.Frontend.usizeStep b p ((hp.lt_iff p).mpr hpl)
  have hb34 : byteAt b p = 34 := byteAt_of_byteL hp p 34 (by decide) hq34
  -- ke := keyEnd b (p + 1)
  obtain ⟨ke, hked⟩ : ∃ ke, ke = keyEnd b (p + 1) := ⟨_, rfl⟩
  have hkeL := keyEnd_eq hp _ (p + 1) rfl
  rw [← hked, hp1] at hkeL
  have lb2 : u2.locals.lookup sB = some (.val (.word A)) := by lk [u2]; rw [lo1 sB (by decide)]; exact lb
  have ln2 : u2.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    lk [u2]; rw [lo1 sN (by decide)]; exact ln
  have lp2 : u2.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))) := by lk [u2]; exact lp1
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 (p + 1).toNat)
    (v := BitVec.ofNat 64 ke.toNat) (w0 := wK) (by decide) (by decide) (by decide) hc1.2.2.2.2.1
    (eval_vv u2 sB _ lb2) (eval_vv u2 sN _ ln2)
    (by rw [eval_add_c u2 sHP _ _ lp2, hp1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
    (by lk [u2]; rw [lo1 sK (by decide)]; exact lK) (fun callee h1 h2 h3 => by
      rw [hked]; exact keyEnd_refines (callEntryStateHOLFinite u2 callee) A b hp
        (bytesAt_congr hb m1 d1 b1) (p + 1) (by omega) hc1.2.2.1 h1 h2 h3) (fun u3 hs3 => ?_)
  obtain ⟨m3, d3, g3, c3, b3, lk3, lo3⟩ := hs3
  have hc3 : HintCodes u3 := hc1.congr c3
  refine retP_ite (eval_eq_c u3 sK ke.toNat 0 (usz_lt ke) (by decide) lk3) (fun _ => retP_hang _ _) (fun hw => ?_)
  have hk0 : ke.toNat ≠ 0 := by intro h; simp [bw, h] at hw
  obtain ⟨hkel, hpke⟩ := keyEndL_lt b.data.toList (p.toNat + 1) (by rw [← hkeL]; exact hk0)
  rw [← hkeL] at hkel hpke
  replace hkel : ke.toNat < b.size := by simpa using hkel
  have hke0 : (ke == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hk0 (by rw [h]; rfl))
  have lb3 : u3.locals.lookup sB = some (.val (.word A)) := by rw [lo3 sB (by decide)]; exact lb2
  have ln3 : u3.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    rw [lo3 sN (by decide)]; exact ln2
  have lp3 : u3.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))) := by
    rw [lo3 sHP (by decide)]; exact lp2
  -- keyAt
  have hkl : (ke - (p + 1)).toNat = ke.toNat - (p.toNat + 1) := by
    rw [USize.toNat_sub_of_le, hp1]; rw [USize.le_iff_toNat_le, hp1]; omega
  refine retP_call4 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 p.toNat)
    (v4 := BitVec.ofNat 64 (ke - (p + 1)).toNat) (v := BitVec.ofNat 64 (keyAt b p (ke - (p + 1))).ctorIdx)
    (w0 := wKK) (by decide) hc3.2.2.2.2.2.2
    (eval_vv u3 sB _ lb3) (eval_vv u3 sN _ ln3) (eval_vv u3 sHP _ lp3)
    (by
      simp [vv, evalHOLExact, evalListHOLExact, lk3, lp3, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hkl]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
    (by rw [lo3 sKK (by decide)]; lk [u2]; rw [lo1 sKK (by decide)]; exact lKK)
    (fun callee h1 h2 h3 h4 => keyAt_refines (callEntryStateHOLFinite u3 callee) A b hp
      (bytesAt_congr hb (m3.trans m1) (d3.trans d1) (b3.trans b1)) p (ke - (p + 1)) (by omega) h1 h2 h3 h4)
    (fun u4 hs4 => ?_)
  obtain ⟨m4, d4, g4, c4, b4, lkk4, lo4⟩ := hs4
  have hc4 : HintCodes u4 := hc3.congr c4
  refine retP_ite (eval_eq_c u4 sKK _ Key.kRegular.ctorIdx
    (by have := key_ctorIdx_lt (keyAt b p (ke - (p + 1))); omega)
    (by have := key_ctorIdx_lt Key.kRegular; omega) lkk4) (fun hw => ?_) (fun _ => retP_hang _ _)
  have hkr : keyAt b p (ke - (p + 1)) = .kRegular := key_ctorIdx_inj (by
    by_cases h : (keyAt b p (ke - (p + 1))).ctorIdx = Key.kRegular.ctorIdx
    · exact h
    · simp [bw, h] at hw)
  have lb4 : u4.locals.lookup sB = some (.val (.word A)) := by rw [lo4 sB (by decide)]; exact lb3
  have ln4 : u4.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    rw [lo4 sN (by decide)]; exact ln3
  have lp4 : u4.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))) := by
    rw [lo4 sHP (by decide)]; exact lp3
  have lk4 : u4.locals.lookup sK = some (.val (.word (BitVec.ofNat 64 ke.toNat))) := by
    rw [lo4 sK (by decide)]; exact lk3
  -- valueAt
  obtain ⟨vv', hvd⟩ : ∃ x, x = valueAt b p ke := ⟨_, rfl⟩
  have hvL := valueAt_eq hp p ke hkel
  rw [← hvd] at hvL
  have hvle : vv'.toNat ≤ b.size := by
    have := valueAtL_le b.data.toList p.toNat ke.toNat (by simp; omega) (by simpa using hkel)
    rw [hvL]; simpa using this
  refine retP_call4 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 p.toNat)
    (v4 := BitVec.ofNat 64 ke.toNat) (v := BitVec.ofNat 64 vv'.toNat)
    (w0 := wV) (by decide) hc4.2.2.2.2.2.1
    (eval_vv u4 sB _ lb4) (eval_vv u4 sN _ ln4) (eval_vv u4 sHP _ lp4) (eval_vv u4 sK _ lk4)
    (by rw [lo4 sV (by decide), lo3 sV (by decide)]; lk [u2]; rw [lo1 sV (by decide)]; exact lV)
    (fun callee h1 h2 h3 h4 => by
      rw [hvd]; exact valueAt_refines (callEntryStateHOLFinite u4 callee) A b hp
        (bytesAt_congr hb (m4.trans (m3.trans m1)) (d4.trans (d3.trans d1)) (b4.trans (b3.trans b1)))
        p ke hkel hc4.1 h1 h2 h3 h4)
    (fun u5 hs5 => ?_)
  obtain ⟨m5, d5, g5, c5, b5, lv5, lo5⟩ := hs5
  have hc5 : HintCodes u5 := hc4.congr c5
  have lp5 : u5.locals.lookup sHP = some (.val (.word (BitVec.ofNat 64 p.toNat))) := by
    rw [lo5 sHP (by decide)]; exact lp4
  have hcmp := ConsLoop.eval_cmp_of u5 .equal (vv sV) (vv sHP) _ _ (eval_vv u5 sV _ lv5) (eval_vv u5 sHP _ lp5)
  rw [bw_eq _ _ (usz_lt vv') (usz_lt p)] at hcmp
  refine retP_ite hcmp (fun _ => retP_hang _ _) (fun hw => ?_)
  have hvp : vv'.toNat ≠ p.toNat := by intro h; simp [bw, h] at hw
  have lb5 : u5.locals.lookup sB = some (.val (.word A)) := by rw [lo5 sB (by decide)]; exact lb4
  have ln5 : u5.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    rw [lo5 sN (by decide)]; exact ln4
  -- numEnd
  obtain ⟨e, hed⟩ : ∃ x, x = numEnd b vv' := ⟨_, rfl⟩
  have heL := numEnd_eq hp vv' hvle
  rw [← hed] at heL
  have hele : e.toNat ≤ b.size := by
    have := numEndL_le b.data.toList vv'.toNat (by simpa using hvle)
    rw [heL]; simpa using this
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 vv'.toNat)
    (v := BitVec.ofNat 64 e.toNat) (w0 := wE) (by decide) (by decide) (by decide) hc5.2.2.2.1
    (eval_vv u5 sB _ lb5) (eval_vv u5 sN _ ln5) (eval_vv u5 sV _ lv5)
    (by rw [lo5 sE2 (by decide), lo4 sE2 (by decide), lo3 sE2 (by decide)]; lk [u2]
        rw [lo1 sE2 (by decide)]; exact lE)
    (fun callee h1 h2 h3 => by
      rw [hed]; exact numEnd_refines (callEntryStateHOLFinite u5 callee) A b hp
        (bytesAt_congr hb (m5.trans (m4.trans (m3.trans m1))) (d5.trans (d4.trans (d3.trans d1)))
          (b5.trans (b4.trans (b3.trans b1)))) vv' hvle hc5.2.1 h1 h2 h3)
    (fun u6 hs6 => ?_)
  obtain ⟨m6, d6, g6, c6, b6, le6, lo6⟩ := hs6
  have hc6 : HintCodes u6 := hc5.congr c6
  have lv6 : u6.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 vv'.toNat))) := by
    rw [lo6 sV (by decide)]; exact lv5
  have hcmp2 := ConsLoop.eval_cmp_of u6 .equal (vv sE2) (vv sV) _ _ (eval_vv u6 sE2 _ le6) (eval_vv u6 sV _ lv6)
  rw [bw_eq _ _ (usz_lt e) (usz_lt vv')] at hcmp2
  refine retP_ite hcmp2 (fun _ => retP_hang _ _) (fun hw => ?_)
  have hev : e.toNat ≠ vv'.toNat := by intro h; simp [bw, h] at hw
  have lb6 : u6.locals.lookup sB = some (.val (.word A)) := by rw [lo6 sB (by decide)]; exact lb5
  have ln6 : u6.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by
    rw [lo6 sN (by decide)]; exact ln5
  -- q := skipWs b e
  obtain ⟨q, hqd⟩ : ∃ x, x = skipWs b e := ⟨_, rfl⟩
  have hqL := skipWs_eq hp _ e rfl
  rw [← hqd] at hqL
  have hqle : q.toNat ≤ b.size := by
    have := skipL_le_length isWsN b.data.toList _ e.toNat rfl (by simpa using hele)
    rw [hqL]; simpa using this
  refine retP_call3 (v1 := A) (v2 := BitVec.ofNat 64 b.size) (v3 := BitVec.ofNat 64 e.toNat)
    (v := BitVec.ofNat 64 q.toNat) (w0 := BitVec.ofNat 64 p.toNat) (by decide) (by decide) (by decide) hc6.1
    (eval_vv u6 sB _ lb6) (eval_vv u6 sN _ ln6) (eval_vv u6 sE2 _ le6)
    (by rw [lo6 sHP (by decide)]; exact lp5)
    (fun callee h1 h2 h3 => by
      rw [hqd]; exact skipWs_refines (callEntryStateHOLFinite u6 callee) A b hp
        (bytesAt_congr hb (m6.trans (m5.trans (m4.trans (m3.trans m1))))
          (d6.trans (d5.trans (d4.trans (d3.trans d1)))) (b6.trans (b5.trans (b4.trans (b3.trans b1)))))
        e hele h1 h2 h3)
    (fun u7 hs7 => ?_)
  obtain ⟨m7, d7, g7, c7, b7, lq7, lo7⟩ := hs7
  have hb7 : BytesAt u7 A b.data.toList := bytesAt_congr hb
    (m7.trans (m6.trans (m5.trans (m4.trans (m3.trans m1)))))
    (d7.trans (d6.trans (d5.trans (d4.trans (d3.trans d1)))))
    (b7.trans (b6.trans (b5.trans (b4.trans (b3.trans b1)))))
  have e8 := bAt_spec u7 A b.data.toList sC (vv sHP) q.toNat hb7 (by omega)
    (BitVec.ofNat 64 (byteL b.data.toList p.toNat).toNat)
    (by rw [lo7 sC (by decide), lo6 sC (by decide), lo5 sC (by decide), lo4 sC (by decide), lo3 sC (by decide)]
        lk [u2])
    (by rw [lo7 sB (by decide)]; exact lb6) (by rw [lo7 sN (by decide)]; simpa using ln6) (eval_vv u7 sHP _ lq7)
  refine retP_seq e8 ?_ rfl rfl rfl rfl rfl
  let u8 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList q.toNat).toNat))) u7
  refine retP_ite (eval_eq_c u8 sC (byteL b.data.toList q.toNat).toNat 125 (by have := UInt8.toNat_lt (byteL b.data.toList q.toNat); omega)
    (by decide) (by lk [u8])) (fun hw => ?_) (fun _ => retP_hang _ _)
  have hq125 : (byteL b.data.toList q.toNat).toNat = 125 := by
    by_cases h : (byteL b.data.toList q.toNat).toNat = 125
    · exact h
    · simp [bw, h] at hw
  have hql : q.toNat < b.size := by have := lt_of_byteL hq125 (by decide); simpa using this
  have hq1 : (q + 1).toNat = q.toNat + 1 := ConLeche.Frontend.usizeStep b q ((hp.lt_iff q).mpr hql)
  have hb125 : byteAt b q = 125 := byteAt_of_byteL hp q 125 (by decide) hq125
  have hret := eval_add_c u8 sHP _ (BitVec.ofNat 64 1) (by lk [u8]; exact lq7)
  have hsum : BitVec.ofNat 64 q.toNat + BitVec.ofNat 64 1 = BitVec.ofNat 64 (q + 1).toNat := by
    rw [hq1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  rw [hsum] at hret
  unfold RetP
  rw [evaluateHOLFiniteState_eq_evaluate_def u8 (.return _)]
  refine Or.inr ⟨BitVec.ofNat 64 (q + 1).toNat, ?_, ⟨q + 1, rfl, by omega, .regular (readNatAt b vv' e), ?_⟩, ?_⟩
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL]
  · have h34 : (byteAt b v == 34) = false := by rw [hbyte]; rfl
    have h123 : (byteAt b v == 123) = true := by rw [hbyte]; rfl
    simp only [scanHints, h34, h123, Bool.false_eq_true, ↓reduceIte, ← hpd, bne_false_of hb34, ← hked, hke0,
      hkr, ← hvd, beq_false_of_toNat hvp, ← hed, beq_false_of_toNat hev, ← hqd, hb125]
    rfl
  · simp [hret, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`scanHints` in Pancake is sound for con-leche's**: when `hiFun` returns `e`, `scanHints`
accepts at `v` and ends at `e`, at most the length. -/
theorem hiFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : HintCodes t) (v : USize) (hv : v.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat)))) :
    RetP t hiFun (HintQ b v) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  unfold hiFun
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t2 := setVarHOLFinite sHP (.val (.word 0)) (setVarHOLFinite sKK (.val (.word 0))
    (setVarHOLFinite sV (.val (.word 0)) (setVarHOLFinite sK (.val (.word 0))
      (setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sC (.val (.word 0)) t)))))
  have e1 := bAt_spec t2 A b.data.toList sC (vv sI) v.toNat (bytesAt_congr hb rfl rfl rfl) (by omega) 0
    (by lk [t2]) (by lk [t2]; exact lb) (by lk [t2]; simpa using ln) (eval_vv t2 sI _ (by lk [t2]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t3 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) t2
  have lb3 : t3.locals.lookup sB = some (.val (.word A)) := by lk [t3, t2]; exact lb
  have ln3 : t3.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by lk [t3, t2]; exact ln
  have li3 : t3.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by lk [t3, t2]; exact li
  have hcv := UInt8.toNat_lt (byteL b.data.toList v.toNat)
  refine retP_ite (eval_eq_c t3 sC (byteL b.data.toList v.toNat).toNat 34 (by omega) (by decide) (by lk [t3])) (fun hw => ?_) (fun hw0 => ?_)
  · have hq : (byteL b.data.toList v.toNat).toNat = 34 := by
      by_cases h : (byteL b.data.toList v.toNat).toNat = 34
      · exact h
      · simp [bw, h] at hw
    have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
    exact hq_sound t3 A b hp (bytesAt_congr hb rfl rfl rfl) v hvl (byteAt_of_byteL hp v 34 (by decide) hq) lb3 ln3 li3
  · refine retP_ite (eval_eq_c t3 sC (byteL b.data.toList v.toNat).toNat 123 (by omega) (by decide) (by lk [t3])) (fun hw => ?_) (fun _ => retP_hang _ _)
    have hq : (byteL b.data.toList v.toNat).toNat = 123 := by
      by_cases h : (byteL b.data.toList v.toNat).toNat = 123
      · exact h
      · simp [bw, h] at hw
    have hvl : v.toNat < b.size := by have := lt_of_byteL hq (by decide); simpa using this
    exact hr_sound t3 A b hp (bytesAt_congr hb rfl rfl rfl) (hc.congr rfl) v hvl
      (byteAt_of_byteL hp v 123 (by decide) hq) lb3 ln3 li3 (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by lk [t3, t2] <;> rfl⟩)

end

end ConPanqueque.Scan
