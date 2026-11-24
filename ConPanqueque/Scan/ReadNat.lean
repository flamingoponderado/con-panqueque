import ConPanqueque.Scan.Skip

/-! # Reading a digit run, saturated

`readNatSat(b, i, e)`: the decimal value of the digits in `[i, e)`, capped at `natCap = 2^62`.
The scanner's numbers are table indices, which a cap at `2^62` decides exactly (no table holds that
many entries); `natVal` literals, which may be long, get their own limb reader. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sE := ofString "e"
def sA := ofString "acc"

/-- `natCap / 10`, rounded up: below it, `acc * 10 + 9` stays below `2^64`. -/
def rnT : Nat := 461168601842738791

def rnBody : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sE))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.seq (.ite (.cmp .lower (vv sA) (.const (BitVec.ofNat 64 rnT)))
          (.seq (.assign .local sA (.op .add [.panop .mul [vv sA, .const 10], .op .sub [vv sC, .const 48]]))
            (.ite (.cmp .lower (.const (BitVec.ofNat 64 natCap)) (vv sA))
              (.assign .local sA (.const (BitVec.ofNat 64 natCap))) .skip))
          (.assign .local sA (.const (BitVec.ofNat 64 natCap))))
        (.assign .local sI (.op .add [vv sI, .const 1]))))
    (.assign .local sG (.const 0))

def rnLoop : ProgHOL 64 := .while (vv sG) rnBody

/-- `readNatSat(b, i, e)`. -/
def rnFun : ProgHOL 64 :=
  .dec sG .one (.const 1) (.dec sC .one (.const 0) (.dec sA .one (.const 0)
    (.seq rnLoop (.return (vv sA)))))

/-- The digits of `[i0, e)`. -/
def DigitsIn (bs : List UInt8) (i0 e : Nat) : Prop :=
  ∀ k (hk : k < bs.length), i0 ≤ k → k < e → isDigitN bs[k].toNat = true

section
variable {σ : Type}

def RnI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 e : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sE = some (.val (.word (BitVec.ofNat 64 e))) ∧
  (∃ c, u.locals.lookup sC = some (.val (.word c))) ∧
  ∃ j acc, i0 ≤ j ∧ j ≤ e ∧ u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) ∧
    u.locals.lookup sA = some (.val (.word (BitVec.ofNat 64 (min acc natCap)))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧
        min (readL bs j e acc) natCap = min (readL bs i0 e 0) natCap) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ min acc natCap = min (readL bs i0 e 0) natCap))

theorem ofNat_lt_iff (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x < BitVec.ofNat 64 y) ↔ x < y := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem eval_lower (u : PanSemStateFiniteExact 64 σ) (l r : ExpHOL 64) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (hl : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) l =
      some (.val (.word (BitVec.ofNat 64 x))))
    (hr : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) r =
      some (.val (.word (BitVec.ofNat 64 y)))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (.cmp .lower l r) =
      some (.val (.word (bw (x < y)))) := by
  rw [ConsLoop.eval_cmp_of u .lower _ _ _ _ hl hr]
  simp only [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : x < y <;> simp [h, ofNat_lt_iff x y hx hy]

theorem skip_eval (u : PanSemStateFiniteExact 64 σ) : evaluateHOLFiniteState u .skip = (none, u) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]

theorem rn_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 e : Nat)
    (hb : BytesAt t A bs) (he : e ≤ bs.length) (hd : DigitsIn bs i0 e)
    (u : PanSemStateFiniteExact 64 σ) (hu : RnI t A bs i0 e u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) rnBody = (none, u') ∧ RnI t A bs i0 e u' := by
  obtain ⟨m0, d0, c0, g0, b0, lb, le, ⟨c, lc⟩, j, acc, hij, hj, li, la, br⟩ := hu
  obtain ⟨_, hsame⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  have hcap : natCap < 2 ^ 64 := by unfold natCap; decide
  have hmin : min acc natCap < 2 ^ 64 := by omega
  let v := decClockHOLFinite u
  have hlt := eval_lower v (vv sI) (vv sE) j e (by omega) (by omega)
    (eval_vv v sI _ (by lk [v]; exact li)) (eval_vv v sE _ (by lk [v]; exact le))
  unfold rnBody
  rw [ite_word v _ _ _ _ hlt]
  by_cases hje : j < e
  · simp only [bw, hje, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hjl : j < bs.length := by omega
    have hdig := hd j hjl hij hje
    have hc48 : 48 ≤ bs[j].toNat ∧ bs[j].toNat ≤ 57 := by
      simp [isDigitN] at hdig; omega
    have hbv : BytesAt v A bs := bytesAt_congr hb m0 d0 b0
    have haddr : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
        (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j))) := by
      have lb' : v.locals.lookup sB = some (.val (.word A)) := by lk [v]; exact lb
      have li' : v.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by lk [v]; exact li
      simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [seq_normal _ (ConsLoop.assign_local v sC _ (BitVec.ofNat 64 bs[j].toNat) c
      (eval_loadByte_bytes v _ A bs j hbv hjl haddr) (by lk [v]; exact lc))]
    let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 bs[j].toNat))) v
    have la1 : v1.locals.lookup sA = some (.val (.word (BitVec.ofNat 64 (min acc natCap)))) := by
      lk [v1, v]; exact la
    have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 bs[j].toNat))) := by lk [v1]
    have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by lk [v1, v]; exact li
    obtain ⟨d, hdd⟩ : ∃ d, d = bs[j].toNat - 48 := ⟨_, rfl⟩
    have hd9 : d ≤ 9 := by omega
    -- the new accumulator, whichever branch computes it
    have key : ∃ v2, evaluateHOLFiniteState v1
        (.ite (.cmp .lower (vv sA) (.const (BitVec.ofNat 64 rnT)))
          (.seq (.assign .local sA (.op .add [.panop .mul [vv sA, .const 10], .op .sub [vv sC, .const 48]]))
            (.ite (.cmp .lower (.const (BitVec.ofNat 64 natCap)) (vv sA))
              (.assign .local sA (.const (BitVec.ofNat 64 natCap))) .skip))
          (.assign .local sA (.const (BitVec.ofNat 64 natCap)))) = (none, v2) ∧
        v2.memory = v1.memory ∧ v2.memaddrs = v1.memaddrs ∧ v2.code = v1.code ∧
        v2.globals = v1.globals ∧ v2.be = v1.be ∧
        v2.locals.lookup sA = some (.val (.word (BitVec.ofNat 64 (min (acc * 10 + d) natCap)))) ∧
        ∀ y, y ≠ sA → v2.locals.lookup y = v1.locals.lookup y := by
      have hT := eval_lower v1 (vv sA) (.const (BitVec.ofNat 64 rnT)) (min acc natCap) rnT hmin
        (by unfold rnT; decide) (eval_vv v1 sA _ la1) (by simp [evalHOLExact])
      rw [ite_word v1 _ _ _ _ hT]
      by_cases hsm : min acc natCap < rnT
      · simp only [bw, hsm, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
        have hnov : min acc natCap * 10 + d < 2 ^ 64 := by unfold rnT at hsm; omega
        have hev : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
            (.op .add [.panop .mul [vv sA, .const 10], .op .sub [vv sC, .const 48]]) =
            some (.val (.word (BitVec.ofNat 64 (min acc natCap * 10 + d)))) := by
          simp [vv, evalHOLExact, evalListHOLExact, la1, lc1, wordOpHOL, wordOp, panOpHOL, valueIsWord,
            valueWord]
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub]
          omega
        rw [seq_normal _ (ConsLoop.assign_local v1 sA _ _ _ hev la1)]
        let v3 := setVarHOLFinite sA (.val (.word (BitVec.ofNat 64 (min acc natCap * 10 + d)))) v1
        have la3 : v3.locals.lookup sA = some (.val (.word (BitVec.ofNat 64 (min acc natCap * 10 + d)))) := by
          lk [v3]
        have hC := eval_lower v3 (.const (BitVec.ofNat 64 natCap)) (vv sA) natCap _ hcap hnov
          (by simp [evalHOLExact]) (eval_vv v3 sA _ la3)
        rw [ite_word v3 _ _ _ _ hC]
        by_cases hov : natCap < min acc natCap * 10 + d
        · simp only [bw, hov, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
          rw [ConsLoop.assign_local v3 sA _ (BitVec.ofNat 64 natCap) _ (by simp [evalHOLExact]) la3]
          have : min (acc * 10 + d) natCap = natCap := by rw [← min_step acc d hd9]; omega
          refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [this]; lk, fun y hy => by lk [v3]⟩
        · simp only [bw, hov, ↓reduceIte, ne_eq, not_true_eq_false]
          rw [skip_eval]
          have : min (acc * 10 + d) natCap = min acc natCap * 10 + d := by
            rw [← min_step acc d hd9]; omega
          refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [this]; exact la3, fun y hy => by lk [v3]⟩
      · simp only [bw, hsm, ↓reduceIte, ne_eq, not_true_eq_false]
        rw [ConsLoop.assign_local v1 sA _ (BitVec.ofNat 64 natCap) _ (by simp [evalHOLExact]) la1]
        have : min (acc * 10 + d) natCap = natCap := by
          unfold rnT at hsm; unfold natCap at *; omega
        refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [this]; lk, fun y hy => by lk⟩
    obtain ⟨v2, hv2, m2, d2, c2, g2, b2, la2, lo2⟩ := key
    rw [seq_normal _ hv2]
    have li2 : v2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by
      rw [lo2 sI (by decide)]; exact li1
    rw [ConsLoop.assign_local v2 sI _ (BitVec.ofNat 64 (j + 1)) _ (by
      rw [eval_add_c v2 sI _ _ li2]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li2]
    refine ⟨_, rfl, m2.trans m0, d2.trans d0, c2.trans c0, g2.trans g0, b2.trans b0,
      by lk; rw [lo2 sB (by decide)]; lk [v1, v]; exact lb,
      by lk; rw [lo2 sE (by decide)]; lk [v1, v]; exact le,
      ⟨BitVec.ofNat 64 bs[j].toNat, by lk; rw [lo2 sC (by decide)]; exact lc1⟩, j + 1, acc * 10 + d,
      by omega, hje, by lk, by lk; exact la2,
      Or.inl ⟨by lk; rw [lo2 sG (by decide)]; lk [v1, v]; exact hg, ?_⟩⟩
    rw [hdd]
    rw [← hsame, readL_step bs j e acc hje hjl]
  · simp only [bw, hje, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [ConsLoop.assign_local v sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v]; exact hg)]
    refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v]; exact lb, by lk [v]; exact le,
      ⟨c, by lk [v]; exact lc⟩, j, acc, hij, hj, by lk [v]; exact li, by lk [v]; exact la,
      Or.inr ⟨by lk, ?_⟩⟩
    rw [← hsame, readL_end bs j e acc hje]

theorem rnLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 e : Nat)
    (hb : BytesAt t A bs) (he : e ≤ bs.length) (hd : DigitsIn bs i0 e)
    (u : PanSemStateFiniteExact 64 σ) (hu : RnI t A bs i0 e u) :
    Stop (evaluateHOLFiniteState u rnLoop).1 ∨ ((evaluateHOLFiniteState u rnLoop).1 = none ∧
      RnI t A bs i0 e (evaluateHOLFiniteState u rnLoop).2 ∧
      (evaluateHOLFiniteState u rnLoop).2.locals.lookup sA =
        some (.val (.word (BitVec.ofNat 64 (min (readL bs i0 e 0) natCap))))) := by
  have := while_stop (vv sG) rnBody (RnI t A bs i0 e)
    (fun u => RnI t A bs i0 e u ∧
      u.locals.lookup sA = some (.val (.word (BitVec.ofNat 64 (min (readL bs i0 e 0) natCap)))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, j, acc, _, _, _, la, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hj⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e', hu'⟩ := rn_step t A bs i0 e hb he hd u hu hg
        rw [e']; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, by rw [la, hj]⟩,
          fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- **`readNatSat` refines `min (readL …) natCap`**: on a digit run `[i0, e)` inside the buffer. -/
theorem rnFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 e : Nat)
    (hb : BytesAt t A bs) (hie : i0 ≤ e) (he : e ≤ bs.length) (hd : DigitsIn bs i0 e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (le : t.locals.lookup sE = some (.val (.word (BitVec.ofNat 64 e))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    Stop (evaluateHOLFiniteState t rnFun).1 ∨
      ((evaluateHOLFiniteState t rnFun).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (min (readL bs i0 e 0) natCap))))) ∧
        (evaluateHOLFiniteState t rnFun).2.memory = t.memory ∧
        (evaluateHOLFiniteState t rnFun).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t rnFun).2.globals = t.globals ∧
        (evaluateHOLFiniteState t rnFun).2.code = t.code) := by
  unfold rnFun
  rw [dec_word_eq t sG _ 1 _ (by simp [evalHOLExact])]
  let t1 := setVarHOLFinite sG (.val (.word 1)) t
  rw [dec_word_eq t1 sC _ 0 _ (by simp [evalHOLExact])]
  let t2 := setVarHOLFinite sC (.val (.word 0)) t1
  rw [dec_word_eq t2 sA _ 0 _ (by simp [evalHOLExact])]
  let t3 := setVarHOLFinite sA (.val (.word 0)) t2
  have h0 : RnI t A bs i0 e t3 := ⟨rfl, rfl, rfl, rfl, rfl, by lk [t3, t2, t1]; exact lb,
    by lk [t3, t2, t1]; exact le, ⟨0, by lk [t3, t2]⟩, i0, 0, Nat.le_refl _, hie,
    by lk [t3, t2, t1]; exact li, by lk [t3]; rfl, Or.inl ⟨by lk [t3, t2, t1], rfl⟩⟩
  rcases rnLoop_spec t A bs i0 e hb he hd t3 h0 with hs | ⟨hn, hI, hres⟩
  · exact Or.inl (seq_stop t3 rnLoop _ hs)
  · right
    obtain ⟨m0, d0, c0, g0, -, -⟩ := hI
    generalize hu : evaluateHOLFiniteState t3 rnLoop = r at hn hres m0 d0 c0 g0
    obtain ⟨r1, r2⟩ := r
    simp only at hn hres m0 d0 c0 g0
    subst hn
    rw [seq_normal _ hu, evaluateHOLFiniteState_eq_evaluate_def r2 (.return _)]
    simp [eval_vv r2 sA _ hres, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
      emptyLocalsHOLFinite, m0, d0, c0, g0]

/-- **`readNatSat` in Pancake is con-leche's `readNatAt`, capped at `natCap`**, on the digit run at
`i` (ending at `e`). -/
theorem rnFun_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i e : USize) (hi : i.toNat ≤ b.size)
    (he : e.toNat = skipDigitsL b.data.toList i.toNat)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (le : t.locals.lookup sE = some (.val (.word (BitVec.ofNat 64 e.toNat))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    Stop (evaluateHOLFiniteState t rnFun).1 ∨
      ((evaluateHOLFiniteState t rnFun).1 = some (.returned (.val (.word
          (BitVec.ofNat 64 (min (ConLeche.Frontend.readNatAt b i e) natCap))))) ∧
        (evaluateHOLFiniteState t rnFun).2.memory = t.memory ∧
        (evaluateHOLFiniteState t rnFun).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t rnFun).2.globals = t.globals ∧
        (evaluateHOLFiniteState t rnFun).2.code = t.code) := by
  have hge := skipL_ge isDigitN b.data.toList _ i.toNat rfl
  have hle := skipL_le_length isDigitN b.data.toList _ i.toNat rfl (by simpa using hi)
  have hall := skipL_all isDigitN b.data.toList _ i.toNat rfl
  simp only [skipDigitsL] at he
  rw [readNatAt_eq hp i e (by simpa [skipDigitsL] using he)]
  exact rnFun_spec t A b.data.toList i.toNat e.toNat hb (by omega) (by omega)
    (fun k hk h1 h2 => hall k hk h1 (by omega)) lb le li

end

end ConPanqueque.Scan
