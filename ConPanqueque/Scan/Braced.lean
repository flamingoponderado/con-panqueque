import ConPanqueque.Scan.ObjFun

/-! # `skipBraced` in Pancake (the header's value)

A `{`/`[`-opened value skipped by bracket depth, stepping over strings.  Soundly restricted: a
string inside must be plain (`isPlainN`), as everywhere else in the port; anything else is
rejected. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sD := ofString "depth"

def brBody : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite (.cmp .equal (vv sC) (.const 34))
        (.seq (callTo sE2 fSkipPlain [vv sB, vv sN, .op .add [vv sI, .const 1]])
          (.seq (bAt sC (vv sE2))
            (.ite (.cmp .equal (vv sC) (.const 34)) (.assign .local sI (.op .add [vv sE2, .const 1])) hang)))
        (.ite (.cmp .equal (vv sC) (.const 10)) hang
          (.ite (.op .or [.cmp .equal (vv sC) (.const (BitVec.ofNat 64 123)), .cmp .equal (vv sC) (.const (BitVec.ofNat 64 91))])
            (.seq (.assign .local sD (.op .add [vv sD, .const 1])) incI)
            (.ite (.op .or [.cmp .equal (vv sC) (.const (BitVec.ofNat 64 125)), .cmp .equal (vv sC) (.const (BitVec.ofNat 64 93))])
              (.ite (.cmp .equal (vv sD) (.const 0)) (.seq incI (.assign .local sG (.const 0)))
                (.seq (.assign .local sD (.op .sub [vv sD, .const 1])) incI))
              incI)))))
    hang

def brLoop : ProgHOL 64 := .while (vv sG) brBody

/-- `skipBraced(b, n, i)` at depth `0`: the position past the matching close. -/
def brFun : ProgHOL 64 :=
  decsOf [(sG, 1), (sD, 0), (sC, 0), (sE2, 0)] (.seq brLoop (.return (vv sI)))

section
variable {σ : Type}

def BrI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (R : USize)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  (∃ w, u.locals.lookup sC = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sE2 = some (.val (.word w))) ∧
  ∃ (j : USize) (d : Nat), j.toNat ≤ b.size ∧ d ≤ j.toNat ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sD = some (.val (.word (BitVec.ofNat 64 d))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ ConLeche.Frontend.skipBraced b j d = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ R = j))

end

section
variable {σ : Type}

theorem br_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : SkipPlainCode t) (R : USize)
    (u : PanSemStateFiniteExact 64 σ) (hu : BrI t A b R u) (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState (decClockHOLFinite u) brBody).1 ∨
      ((evaluateHOLFiniteState (decClockHOLFinite u) brBody).1 = none ∧
        BrI t A b R (evaluateHOLFiniteState (decClockHOLFinite u) brBody).2) := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, ⟨wc, lc⟩, ⟨we, le⟩, j, d, hj, hd, li, ld, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  let v0 := decClockHOLFinite u
  have hlt := eval_lower v0 (vv sI) (vv sN) j.toNat b.size (by omega) hL
    (eval_vv v0 sI _ (by lk [v0]; exact li)) (eval_vv v0 sN _ (by lk [v0]; exact ln))
  unfold brBody
  rw [ite_word v0 _ _ _ _ hlt]
  by_cases hjl0 : ¬ j.toNat < b.size
  · simp only [bw, hjl0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v0)
  have hjl : j.toNat < b.size := by omega
  simp only [bw, hjl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
  have hju : j < b.usize := (hp.lt_iff j).mpr hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := ConLeche.Frontend.usizeStep b j hju
  have hbv : BytesAt v0 A b.data.toList := bytesAt_congr hb m0 d0 b0
  have haddr : @evalHOLExact 64 σ _ v0.toExact (fun a => Classical.propDecidable (v0.memaddrs a))
      (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j.toNat))) := by
    have lb' : v0.locals.lookup sB = some (.val (.word A)) := by lk [v0]; exact lb
    have li' : v0.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v0]; exact li
    simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨c, hcx⟩ : ∃ c, c = b.data.toList[j.toNat] := ⟨_, rfl⟩
  rw [seq_normal _ (ConsLoop.assign_local v0 sC _ (BitVec.ofNat 64 c.toNat) wc
    (by rw [hcx]; exact eval_loadByte_bytes v0 _ A b.data.toList j.toNat hbv hjl' haddr) (by lk [v0]; exact lc))]
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 c.toNat))) v0
  have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c.toNat))) := by lk [v1]
  have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v1, v0]; exact li
  have ld1 : v1.locals.lookup sD = some (.val (.word (BitVec.ofNat 64 d))) := by lk [v1, v0]; exact ld
  have lg1 : v1.locals.lookup sG = some (.val (.word 1)) := by lk [v1, v0]; exact hg
  have le1 : v1.locals.lookup sE2 = some (.val (.word we)) := by lk [v1, v0]; exact le
  have lb1 : v1.locals.lookup sB = some (.val (.word A)) := by lk [v1, v0]; exact lb
  have ln1 : v1.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) := by lk [v1, v0]; exact ln
  have hct : c.toNat < 256 := UInt8.toNat_lt c
  have hstep := ConLeche.Frontend.skipBraced.eq_def b j d
  rw [dif_pos hju, uget_eq b j hjl hju, ← hcx] at hstep
  simp only at hstep
  have mk : ∀ (w : PanSemStateFiniteExact 64 σ) (j' : USize) (d' : Nat),
      w.memory = v1.memory → w.memaddrs = v1.memaddrs → w.code = v1.code → w.globals = v1.globals →
      w.be = v1.be → (∀ y, y ∉ [sI, sD, sG, sE2, sC] → w.locals.lookup y = v1.locals.lookup y) →
      (∃ w', w.locals.lookup sC = some (.val (.word w'))) → (∃ w', w.locals.lookup sE2 = some (.val (.word w'))) →
      j'.toNat ≤ b.size → d' ≤ j'.toNat →
      w.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j'.toNat))) →
      w.locals.lookup sD = some (.val (.word (BitVec.ofNat 64 d'))) →
      ((w.locals.lookup sG = some (.val (.word 1)) ∧ ConLeche.Frontend.skipBraced b j' d' = R) ∨
       (w.locals.lookup sG = some (.val (.word 0)) ∧ R = j')) → BrI t A b R w := by
    intro w j' d' a1 a2 a3 a4 a5 hlo hc' he' hj' hd' li' ld' hg'
    exact ⟨a1.trans m0, a2.trans d0, a3.trans c0, a4.trans g0, a5.trans b0,
      by rw [hlo sB (by decide)]; exact lb1, by rw [hlo sN (by decide)]; exact ln1, hc', he', j', d', hj', hd',
      li', ld', hg'⟩
  have hbq : ∀ k : Nat, k < 256 → (c == UInt8.ofNat k) = decide (c.toNat = k) := fun k hk => by
    rw [beq_ofNat c k hk]; by_cases h : c.toNat = k <;> simp [h]
  have incOK : ∀ (w : PanSemStateFiniteExact 64 σ), w.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) →
      evaluateHOLFiniteState w incI = (none, setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) w) :=
    fun w h => ConsLoop.assign_local w sI _ _ _ (by
      rw [eval_add_c w sI _ _ h, hj1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega) h
  -- the string case
  simp only [show (34 : BitVec 64) = BitVec.ofNat 64 34 from rfl, show (10 : BitVec 64) = BitVec.ofNat 64 10 from rfl,
    show (123 : BitVec 64) = BitVec.ofNat 64 123 from rfl, show (91 : BitVec 64) = BitVec.ofNat 64 91 from rfl,
    show (125 : BitVec 64) = BitVec.ofNat 64 125 from rfl, show (93 : BitVec 64) = BitVec.ofNat 64 93 from rfl,
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl]
  rw [ite_word v1 _ _ _ _ (eval_eq_c v1 sC c.toNat 34 (by omega) (by decide) lc1)]
  by_cases h34 : c.toNat = 34
  · simp only [bw, h34, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, hbq 34 (by decide), decide_eq_true h34] at hstep
    simp only [↓reduceIte] at hstep
    have hle := skipL_le_length isPlainN b.data.toList _ (j.toNat + 1) rfl (by simp; omega)
    have hge := skipL_ge isPlainN b.data.toList _ (j.toNat + 1) rfl
    have hall := skipL_all isPlainN b.data.toList _ (j.toNat + 1) rfl
    have hcall := call3_ret v1 sE2 fSkipPlain sB sN sI (skFun plainTest) (vv sB) (vv sN) (.op .add [vv sI, .const 1])
      A (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 (j.toNat + 1))
      (BitVec.ofNat 64 (skipL isPlainN b.data.toList (j.toNat + 1))) we (by decide) (by decide) (by decide)
      (by show u.code.lookup _ = _; rw [c0]; exact hc) (eval_vv v1 sB _ lb1) (eval_vv v1 sN _ ln1)
      (by rw [eval_add_c v1 sI _ _ li1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
      le1
      (fun callee h1 h2 h3 => skFun_spec isPlainN plainTest plainTest_ok _ A b.data.toList (j.toNat + 1)
        (bytesAt_congr hb (by exact m0) (by exact d0) (by exact b0)) (by simp; omega) h1
        (by have : b.data.toList.length = b.size := by simp
            rw [this]; exact h2) h3)
    unfold callTo
    rcases hcall with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, le2, lo1⟩
    · exact Or.inl (seq_stop v1 _ _ hs)
    rw [seq_normal _ hu1]
    obtain ⟨E, hE⟩ : ∃ E, E = skipL isPlainN b.data.toList (j.toNat + 1) := ⟨_, rfl⟩
    rw [← hE] at le2 hle hge
    have e2 := bAt_spec u1 A b.data.toList sC (vv sE2) E (bytesAt_congr hb (m1.trans m0) (d1.trans d0) (b1.trans b0))
      (by simp at hle; omega) _ (by rw [lo1 sC (by decide)]; exact lc1) (by rw [lo1 sB (by decide)]; exact lb1)
      (by rw [lo1 sN (by decide)]; simpa using ln1) (eval_vv u1 sE2 _ le2)
    rw [seq_normal _ e2]
    let u2 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList E).toNat))) u1
    rw [ite_word u2 _ _ _ _ (eval_eq_c u2 sC (byteL b.data.toList E).toNat 34 (by have := UInt8.toNat_lt (byteL b.data.toList E); omega)
      (by decide) (by lk [u2]))]
    by_cases hq : ¬ (byteL b.data.toList E).toNat = 34
    · simp only [bw, hq, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u2)
    have hq' : (byteL b.data.toList E).toNat = 34 := by omega
    simp only [bw, hq', ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hEl : E < b.size := by
      by_cases h : E < b.size
      · exact h
      · simp [byteL, List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ E)] at hq'
    have hEU : (USize.ofNat E).toNat = E := by
      rw [USize.toNat_ofNat']; simp only [USize.size_eq_two_pow, hp.bits]; exact Nat.mod_eq_of_lt (by omega)
    have hclose := strClose_plain hp (USize.ofNat E) (by rw [hEU]; exact hEl)
      (by simp only [hEU]; apply UInt8.toNat_inj.mp
          simpa [byteL, List.getElem?_eq_getElem (by simpa using hEl : E < b.data.toList.length)] using hq')
      _ (j + 1) rfl (by rw [hj1, hEU]; omega) (fun k hk h1 h2 => hall k hk (by rw [hj1] at h1; omega)
        (by rw [hEU] at h2; omega))
    rw [hclose] at hstep
    have hE1 : (USize.ofNat E + 1).toNat = E + 1 := by
      rw [ConLeche.Frontend.usizeStep b _ ((hp.lt_iff _).mpr (by rw [hEU]; exact hEl)), hEU]
    have hne0 : (USize.ofNat E == 0) = false := beq_eq_false_iff_ne.mpr (fun h => by
      have := congrArg USize.toNat h; rw [hEU] at this; simp at this; omega)
    rw [hne0] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
    rw [dif_pos (USize.lt_iff_toNat_lt.mpr (by rw [hE1]; omega))] at hstep
    have li2 : u2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
      lk [u2]; rw [lo1 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local u2 sI _ (BitVec.ofNat 64 (USize.ofNat E + 1).toNat) _ (by
      rw [eval_add_c u2 sE2 _ _ (by lk [u2]; exact le2), hE1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li2]
    refine Or.inr ⟨rfl, mk _ (USize.ofNat E + 1) d m1 d1 k1 g1 b1 (fun y hy => ?_) ⟨BitVec.ofNat 64 (byteL b.data.toList E).toNat, by lk [u2]⟩ ⟨_, by lk [u2]; exact le2⟩
      (by rw [hE1]; omega) (by rw [hE1]; omega) (by lk) (by lk [u2]; rw [lo1 sD (by decide)]; exact ld1)
      (Or.inl ⟨by lk [u2]; rw [lo1 sG (by decide)]; exact lg1, by rw [← hR, hstep]⟩)⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
    show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u1)).locals.lookup y = _
    rw [lookup_setVar_other _ _ hy.1, lookup_setVar_other _ _ hy.2.2.2.2, lo1 y hy.2.2.2.1]
  simp only [bw, h34, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, hbq 34 (by decide), decide_eq_false h34] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  -- the newline
  rw [ite_word v1 _ _ _ _ (eval_eq_c v1 sC c.toNat 10 (by omega) (by decide) lc1)]
  by_cases h10 : c.toNat = 10
  · simp only [bw, h10, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang v1)
  simp only [bw, h10, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [show (10 : UInt8) = UInt8.ofNat 10 from rfl, hbq 10 (by decide), decide_eq_false h10] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  -- the opening brackets
  have hopen : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.op .or [.cmp .equal (vv sC) (.const (BitVec.ofNat 64 123)), .cmp .equal (vv sC) (.const (BitVec.ofNat 64 91))]) =
      some (.val (.word (bw (c.toNat = 123 ∨ c.toNat = 91)))) := by
    rw [evalHOLExact]
    simp only [evalListHOLExact, show (123 : BitVec 64) = BitVec.ofNat 64 123 from rfl,
      show (91 : BitVec 64) = BitVec.ofNat 64 91 from rfl, eval_eq_c v1 sC c.toNat 123 (by omega) (by decide) lc1,
      eval_eq_c v1 sC c.toNat 91 (by omega) (by decide) lc1]
    simp [valueIsWord, valueWord, bw_or]
  rw [ite_word v1 _ _ _ _ hopen]
  rw [show (123 : UInt8) = UInt8.ofNat 123 from rfl, show (91 : UInt8) = UInt8.ofNat 91 from rfl,
    hbq 123 (by decide), hbq 91 (by decide)] at hstep
  have ld1' := ld1
  by_cases hop : c.toNat = 123 ∨ c.toNat = 91
  · simp only [bw, hop, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have : (decide (c.toNat = 123) || decide (c.toNat = 91)) = true := by rcases hop with h | h <;> simp [h]
    rw [this] at hstep; simp only [↓reduceIte] at hstep
    rw [seq_normal _ (ConsLoop.assign_local v1 sD _ (BitVec.ofNat 64 (d + 1)) _ (by
      rw [eval_add_c v1 sD _ _ ld1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega) ld1)]
    let w1 := setVarHOLFinite sD (.val (.word (BitVec.ofNat 64 (d + 1)))) v1
    rw [incOK w1 (by lk [w1]; exact li1)]
    refine Or.inr ⟨rfl, mk _ (j + 1) (d + 1) rfl rfl rfl rfl rfl (fun y hy => ?_) ⟨_, by lk [w1]; exact lc1⟩
      ⟨_, by lk [w1]; exact le1⟩ (by omega) (by omega) (by lk) (by lk [w1])
      (Or.inl ⟨by lk [w1]; exact lg1, by rw [← hR, hstep]⟩)⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
    show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
    rw [lookup_setVar_other _ _ hy.1, lookup_setVar_other _ _ hy.2.1]
  simp only [bw, hop, ↓reduceIte, ne_eq, not_true_eq_false]
  have : (decide (c.toNat = 123) || decide (c.toNat = 91)) = false := by simp only [not_or] at hop; simp [hop.1, hop.2]
  rw [this] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  -- the closing brackets
  have hclose : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.op .or [.cmp .equal (vv sC) (.const (BitVec.ofNat 64 125)), .cmp .equal (vv sC) (.const (BitVec.ofNat 64 93))]) =
      some (.val (.word (bw (c.toNat = 125 ∨ c.toNat = 93)))) := by
    rw [evalHOLExact]
    simp only [evalListHOLExact, show (125 : BitVec 64) = BitVec.ofNat 64 125 from rfl,
      show (93 : BitVec 64) = BitVec.ofNat 64 93 from rfl, eval_eq_c v1 sC c.toNat 125 (by omega) (by decide) lc1,
      eval_eq_c v1 sC c.toNat 93 (by omega) (by decide) lc1]
    simp [valueIsWord, valueWord, bw_or]
  rw [ite_word v1 _ _ _ _ hclose]
  rw [show (125 : UInt8) = UInt8.ofNat 125 from rfl, show (93 : UInt8) = UInt8.ofNat 93 from rfl,
    hbq 125 (by decide), hbq 93 (by decide)] at hstep
  by_cases hcl : c.toNat = 125 ∨ c.toNat = 93
  · simp only [bw, hcl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have : (decide (c.toNat = 125) || decide (c.toNat = 93)) = true := by rcases hcl with h | h <;> simp [h]
    rw [this] at hstep; simp only [↓reduceIte] at hstep
    rw [ite_word v1 _ _ _ _ (eval_eq_c v1 sD d 0 (by omega) (by decide) ld1)]
    by_cases hd0 : d = 0
    · subst hd0
      simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true] at hstep ⊢
      rw [seq_normal _ (incOK v1 li1)]
      let w1 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1
      rw [ConsLoop.assign_local w1 sG (.const (BitVec.ofNat 64 0)) (BitVec.ofNat 64 0) 1 (by simp [evalHOLExact]) (by lk [w1]; exact lg1)]
      refine Or.inr ⟨rfl, mk _ (j + 1) 0 rfl rfl rfl rfl rfl (fun y hy => ?_) ⟨_, by lk [w1]; exact lc1⟩
        ⟨_, by lk [w1]; exact le1⟩ (by omega) (by omega) (by lk [w1]) (by lk [w1]; exact ld1)
        (Or.inr ⟨by lk [w1]; rfl, by rw [← hR, hstep]⟩)⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
      rw [lookup_setVar_other _ _ hy.2.2.1, lookup_setVar_other _ _ hy.1]
    · simp only [bw, hd0, ↓reduceIte, ne_eq, not_true_eq_false]
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      simp only at hstep
      rw [seq_normal _ (ConsLoop.assign_local v1 sD _ (BitVec.ofNat 64 d') _ (by
        rw [eval_sub_c v1 sD _ _ ld1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ld1)]
      let w1 := setVarHOLFinite sD (.val (.word (BitVec.ofNat 64 d'))) v1
      rw [incOK w1 (by lk [w1]; exact li1)]
      refine Or.inr ⟨rfl, mk _ (j + 1) d' rfl rfl rfl rfl rfl (fun y hy => ?_) ⟨_, by lk [w1]; exact lc1⟩
        ⟨_, by lk [w1]; exact le1⟩ (by omega) (by omega) (by lk) (by lk [w1])
        (Or.inl ⟨by lk [w1]; exact lg1, by rw [← hR, hstep]⟩)⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
      rw [lookup_setVar_other _ _ hy.1, lookup_setVar_other _ _ hy.2.1]
  simp only [bw, hcl, ↓reduceIte, ne_eq, not_true_eq_false]
  have : (decide (c.toNat = 125) || decide (c.toNat = 93)) = false := by simp only [not_or] at hcl; simp [hcl.1, hcl.2]
  rw [this] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  rw [incOK v1 li1]
  refine Or.inr ⟨rfl, mk _ (j + 1) d rfl rfl rfl rfl rfl (fun y hy => ?_) ⟨_, by lk; exact lc1⟩
    ⟨_, by lk; exact le1⟩ (by omega) (by omega) (by lk) (by lk; exact ld1)
    (Or.inl ⟨by lk; exact lg1, by rw [← hR, hstep]⟩)⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
  exact lookup_setVar_other _ _ hy.1

theorem brLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : SkipPlainCode t) (R : USize)
    (u : PanSemStateFiniteExact 64 σ) (hu : BrI t A b R u) :
    Stop (evaluateHOLFiniteState u brLoop).1 ∨ ((evaluateHOLFiniteState u brLoop).1 = none ∧
      BrI t A b R (evaluateHOLFiniteState u brLoop).2 ∧ R.toNat ≤ b.size ∧
      (evaluateHOLFiniteState u brLoop).2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 R.toNat)))) := by
  have := while_stop (vv sG) brBody (BrI t A b R)
    (fun u => BrI t A b R u ∧ R.toNat ≤ b.size ∧
      u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 R.toNat))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, _, j, _, hj, _, li, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hj'⟩
      · exact ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide),
          fun _ _ => br_step t A b hp hb hc R u hu hg⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, by rw [hj']; exact hj, by rw [li, hj']⟩,
          fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4⟩

/-- **`skipBraced` is sound**: started at a position at most the length, the function stops or
returns `skipBraced b i 0`, at most the length, with the frame unchanged. -/
theorem brFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : SkipPlainCode t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t brFun (fun w => ∃ e : USize, w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size ∧
      ConLeche.Frontend.skipBraced b i 0 = e) := by
  unfold brFun
  apply retP_decsOf
  simp only [List.foldl]
  let t2 := setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sC (.val (.word 0))
    (setVarHOLFinite sD (.val (.word 0)) (setVarHOLFinite sG (.val (.word 1)) t)))
  have h0 : BrI t A b (ConLeche.Frontend.skipBraced b i 0) t2 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by lk [t2]; exact lb, by lk [t2]; exact ln, ⟨0, by lk [t2]⟩, ⟨0, by lk [t2]⟩,
      i, 0, hi, Nat.zero_le _, by lk [t2]; exact li, by lk [t2]; rfl, Or.inl ⟨by lk [t2], rfl⟩⟩
  rcases brLoop_spec t A b hp hb hc _ t2 h0 with hs | ⟨hn, hI, hle, hres⟩
  · exact Or.inl (seq_stop t2 brLoop _ hs)
  · right
    obtain ⟨m0, d0, c0, g0, b0, -⟩ := hI
    generalize hu : evaluateHOLFiniteState t2 brLoop = r at hn hres m0 d0 c0 g0 b0
    obtain ⟨r1, r2⟩ := r
    simp only at hn hres m0 d0 c0 g0 b0
    subst hn
    rw [seq_normal _ hu, evaluateHOLFiniteState_eq_evaluate_def r2 (.return _)]
    refine ⟨BitVec.ofNat 64 (ConLeche.Frontend.skipBraced b i 0).toNat, ?_, ⟨_, rfl, hle, rfl⟩, ?_⟩
    · simp [eval_vv r2 sI _ hres, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL]
    · simp [eval_vv r2 sI _ hres, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
        emptyLocalsHOLFinite, m0, d0, c0, g0, b0] <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end ConPanqueque.Scan
