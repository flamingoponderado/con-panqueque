import ConPanqueque.Scan.Lits

/-! # `scanNatList` in Pancake

A validator: it returns the position after the list (the values are read again where they are
used), and rejects whatever con-leche's `scanNatList` rejects.  Its invariant says that con-leche's
loop, resumed at the current position with some accumulator, gives the same answer as from the
start. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sW := ofString "want"
def sNe := ofString "nonempty"
def fNumEnd := ofString "numEnd"

def NumEndCode {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code.lookup fNumEnd = some ([(sB, .one), (sN, .one), (sI, .one)], neFun, .one)

def incI : ProgHOL 64 := .assign .local sI (.op .add [vv sI, .const 1])

def nlBody : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite wsTest incI
        (.ite (.cmp .equal (vv sC) (.const 93))
          (.ite (.op .and [vv sW, vv sNe]) hang (.seq incI (.assign .local sG (.const 0))))
          (.ite (.cmp .equal (vv sC) (.const 44))
            (.ite (vv sW) hang (.seq (.assign .local sW (.const 1)) incI))
            (.ite digitTest
              (.ite (vv sW)
                (.seq (.call (some (some (.local, sE2), none)) fNumEnd [vv sB, vv sN, vv sI])
                  (.ite (.cmp .equal (vv sE2) (vv sI)) hang
                    (.ite (.cmp .lower (vv sI) (vv sE2))
                      (.seq (.assign .local sNe (.const 1))
                        (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2))))
                      hang)))
                hang)
              hang)))))
    hang

def nlLoop : ProgHOL 64 := .while (vv sG) nlBody

/-- `scanNatList(b, n, i)`: the position after the list at `i`. -/
def nlFun : ProgHOL 64 :=
  .dec sG .one (.const 1) (.dec sW .one (.const 1) (.dec sNe .one (.const 0)
    (.dec sC .one (.const 0) (.dec sE2 .one (.const 0)
      (.seq (bAt sC (vv sI))
        (.ite (.cmp .equal (vv sC) (.const 91))
          (.seq incI (.seq nlLoop (.return (vv sI))))
          hang))))))

section
variable {σ : Type}

/-- The loop's invariant, at con-leche's own loop. -/
def NlI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (R : ConLeche.Frontend.ScanRes (List Nat))
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  (∃ w, u.locals.lookup sC = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sE2 = some (.val (.word w))) ∧
  ∃ (j : USize) (acc : List Nat) (wi : Bool), j.toNat ≤ b.size ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sW = some (.val (.word (bw (wi = true)))) ∧
    u.locals.lookup sNe = some (.val (.word (bw (acc ≠ [])))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ ConLeche.Frontend.scanNatListLoop b j acc wi = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok acc.reverse j))

theorem stop_hang (u : PanSemStateFiniteExact 64 σ) : Stop (evaluateHOLFiniteState u hang).1 := by
  rw [hang_spec u.clock u rfl]; exact stop_timeOut


theorem skipDigitsCode_entry {s t : PanSemStateFiniteExact 64 σ} (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (h : SkipDigitsCode t) (hc : s.code = t.code) : SkipDigitsCode (callEntryStateHOLFinite s callee) := by
  unfold SkipDigitsCode at h ⊢; simp only [callEntryStateHOLFinite]; rw [hc]; exact h

theorem bw_and (p q : Prop) [Decidable p] [Decidable q] :
    wordOpHOL .and [bw p, bw q] = some (bw (p ∧ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, bw, wordOpHOL, wordOp] <;> decide

theorem eval_eq_c (u : PanSemStateFiniteExact 64 σ) (x : MlS) (c : Nat) (k : Nat) (hc : c < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : u.locals.lookup x = some (.val (.word (BitVec.ofNat 64 c)))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.cmp .equal (vv x) (.const (BitVec.ofNat 64 k))) = some (.val (.word (bw (c = k)))) := by
  rw [ConsLoop.eval_cmp_of u .equal _ _ (BitVec.ofNat 64 c) (BitVec.ofNat 64 k) (eval_vv u x _ h)
    (by simp [evalHOLExact]), bw_eq c k hc hk]


theorem numEndL_le (bs : List UInt8) (i : Nat) (hi : i ≤ bs.length) : numEndL bs i ≤ bs.length := by
  have := skipL_le_length isDigitN bs _ i rfl hi
  unfold numEndL skipDigitsL; simp only
  split
  · exact hi
  split
  · exact hi
  · exact this

theorem nl_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (R : ConLeche.Frontend.ScanRes (List Nat))
    (hb : BytesAt t A b.data.toList) (hc : NumEndCode t) (hc2 : SkipDigitsCode t)
    (u : PanSemStateFiniteExact 64 σ) (hu : NlI t A b R u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState (decClockHOLFinite u) nlBody).1 ∨
      ((evaluateHOLFiniteState (decClockHOLFinite u) nlBody).1 = none ∧
        NlI t A b R (evaluateHOLFiniteState (decClockHOLFinite u) nlBody).2) := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, ⟨wc, lc⟩, ⟨we, le⟩, j, acc, wi, hj, li, lw, lne, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  let v := decClockHOLFinite u
  have hlt := eval_lower v (vv sI) (vv sN) j.toNat b.size (by omega) hL
    (eval_vv v sI _ (by lk [v]; exact li)) (eval_vv v sN _ (by lk [v]; exact ln))
  unfold nlBody
  rw [ite_word v _ _ _ _ hlt]
  by_cases hjl0 : ¬ j.toNat < b.size
  · simp only [bw, hjl0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v)
  have hjl : j.toNat < b.size := by omega
  simp only [bw, hjl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
  have hju : j < b.usize := (hp.lt_iff j).mpr hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := ConLeche.Frontend.usizeStep b j hju
  have hbv : BytesAt v A b.data.toList := bytesAt_congr hb m0 d0 b0
  have haddr : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j.toNat))) := by
    have lb' : v.locals.lookup sB = some (.val (.word A)) := by lk [v]; exact lb
    have li' : v.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v]; exact li
    simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨c, hcx⟩ : ∃ c, c = b.data.toList[j.toNat] := ⟨_, rfl⟩
  rw [seq_normal _ (ConsLoop.assign_local v sC _ (BitVec.ofNat 64 c.toNat) wc
    (by rw [hcx]; exact eval_loadByte_bytes v _ A b.data.toList j.toNat hbv hjl' haddr) (by lk [v]; exact lc))]
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 c.toNat))) v
  have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c.toNat))) := by lk [v1]
  have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v1, v]; exact li
  -- con-leche's loop, one step
  have hstep := ConLeche.Frontend.scanNatListLoop.eq_1 b j acc wi
  rw [dif_pos hju, uget_eq b j hjl hju, ← hcx] at hstep
  simp only at hstep
  have hct : c.toNat < 256 := UInt8.toNat_lt c
  -- the frame of every normal outcome
  have frame : ∀ (u' : PanSemStateFiniteExact 64 σ), u'.memory = v1.memory → u'.memaddrs = v1.memaddrs →
      u'.code = v1.code → u'.globals = v1.globals → u'.be = v1.be →
      u'.locals.lookup sB = some (.val (.word A)) → u'.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) →
      (∃ w, u'.locals.lookup sC = some (.val (.word w))) → (∃ w, u'.locals.lookup sE2 = some (.val (.word w))) →
      (∃ (j : USize) (acc : List Nat) (wi : Bool), j.toNat ≤ b.size ∧
        u'.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
        u'.locals.lookup sW = some (.val (.word (bw (wi = true)))) ∧
        u'.locals.lookup sNe = some (.val (.word (bw (acc ≠ [])))) ∧
        ((u'.locals.lookup sG = some (.val (.word 1)) ∧ ConLeche.Frontend.scanNatListLoop b j acc wi = R) ∨
         (u'.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok acc.reverse j))) →
      NlI t A b R u' := fun u' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
    ⟨a1.trans m0, a2.trans d0, a3.trans c0, a4.trans g0, a5.trans b0, a6, a7, a8, a9, a10⟩
  rw [ite_word v1 _ _ _ _ (wsTest_ok v1 c.toNat hct lc1)]
  by_cases hws : isWsN c.toNat = true
  · simp only [bw, hws, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [incI, ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
      rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1]
    rw [isWs_eq, hws] at hstep; simp only [↓reduceIte] at hstep
    refine Or.inr ⟨rfl, frame _ rfl rfl rfl rfl rfl (by lk [v1, v]; exact lb) (by lk [v1, v]; exact ln)
      ⟨BitVec.ofNat 64 c.toNat, by lk [v1]⟩ ⟨we, by lk [v1, v]; exact le⟩ ⟨j + 1, acc, wi, by omega, by lk, by lk [v1, v]; exact lw,
        by lk [v1, v]; exact lne, Or.inl ⟨by lk [v1, v]; exact hg, by rw [← hR, hstep]⟩⟩⟩
  simp only [bw, hws, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [isWs_eq] at hstep; simp only [hws, Bool.false_eq_true, ↓reduceIte] at hstep
  have hc93 := eval_eq_c v1 sC c.toNat 93 (by omega) (by decide) lc1
  simp only [show (93 : BitVec 64) = BitVec.ofNat 64 93 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc93]
  have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wi = true)))) := by lk [v1, v]; exact lw
  have lne1 : v1.locals.lookup sNe = some (.val (.word (bw (acc ≠ [])))) := by lk [v1, v]; exact lne
  have lg1 : v1.locals.lookup sG = some (.val (.word 1)) := by lk [v1, v]; exact hg
  by_cases h93 : c.toNat = 93
  · simp only [bw, h93, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc93' : (c == 93) = true := by rw [show (93 : UInt8) = UInt8.ofNat 93 from rfl, beq_ofNat c 93 (by decide)]; simp [h93]
    rw [hc93'] at hstep; simp only [↓reduceIte] at hstep
    have hand : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.op .and [vv sW, vv sNe]) = some (.val (.word (bw (wi = true ∧ acc ≠ [])))) := by
      rw [evalHOLExact]; simp only [evalListHOLExact, eval_vv v1 sW _ lw1, eval_vv v1 sNe _ lne1]
      simp [valueIsWord, valueWord, bw_and]
    rw [ite_word v1 _ _ _ _ hand]
    by_cases hbad : wi = true ∧ acc ≠ []
    · simp only [bw, hbad, ne_eq, not_false_eq_true, and_self, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 from by decide]
      exact Or.inl (stop_hang v1)
    · simp only [bw, hbad, ↓reduceIte, ne_eq, not_true_eq_false]
      have hok : (wi && !acc.isEmpty) = false := by
        cases wi <;> cases acc <;> simp_all
      rw [hok] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
      unfold incI
      rw [seq_normal _ (ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
        rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li1)]
      let v2 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1
      rw [ConsLoop.assign_local v2 sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v2]; exact lg1)]
      refine Or.inr ⟨rfl, frame _ rfl rfl rfl rfl rfl (by lk [v2, v1, v]; exact lb) (by lk [v2, v1, v]; exact ln)
        ⟨BitVec.ofNat 64 c.toNat, by lk [v2, v1]⟩ ⟨we, by lk [v2, v1, v]; exact le⟩
        ⟨j + 1, acc, wi, by omega, by lk [v2], by lk [v2]; exact lw1, by lk [v2]; exact lne1,
          Or.inr ⟨by lk, by rw [← hR, hstep]⟩⟩⟩
  simp only [bw, h93, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc93' : (c == 93) = false := by
    rw [show (93 : UInt8) = UInt8.ofNat 93 from rfl, beq_ofNat c 93 (by decide)]; simp [h93]
  rw [hc93'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  have hc44 := eval_eq_c v1 sC c.toNat 44 (by omega) (by decide) lc1
  simp only [show (44 : BitVec 64) = BitVec.ofNat 64 44 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc44]
  by_cases h44 : c.toNat = 44
  · simp only [bw, h44, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc44' : (c == 44) = true := by rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
    rw [hc44'] at hstep; simp only [↓reduceIte] at hstep
    rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
    cases wi
    · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at hstep ⊢
      rw [seq_normal _ (ConsLoop.assign_local v1 sW (.const 1) 1 0 (by simp [evalHOLExact]) lw1)]
      let v2 := setVarHOLFinite sW (.val (.word 1)) v1
      have li2 : v2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v2]; exact li1
      rw [incI, ConsLoop.assign_local v2 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
        rw [eval_add_c v2 sI _ _ li2, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li2]
      refine Or.inr ⟨rfl, frame _ rfl rfl rfl rfl rfl (by lk [v2, v1, v]; exact lb) (by lk [v2, v1, v]; exact ln)
        ⟨BitVec.ofNat 64 c.toNat, by lk [v2, v1]⟩ ⟨we, by lk [v2, v1, v]; exact le⟩
        ⟨j + 1, acc, true, by omega, by lk, by lk [v2]; rfl, by lk [v2]; exact lne1,
          Or.inl ⟨by lk [v2]; exact lg1, by rw [← hR, hstep]⟩⟩⟩
    · simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (stop_hang v1)
  simp only [bw, h44, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc44' : (c == 44) = false := by
    rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
  rw [hc44'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  rw [ite_word v1 _ _ _ _ (digitTest_ok v1 c.toNat hct lc1)]
  by_cases hdg0 : ¬ isDigitN c.toNat = true
  · simp only [bw, hdg0, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  have hdg : isDigitN c.toNat = true := by simpa using hdg0
  simp only [bw, hdg, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  rw [isDigit_eq, hdg] at hstep; simp only [↓reduceIte] at hstep
  rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
  cases wi
  · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
  have hcode1 : v1.code.lookup fNumEnd = some ([(sB, .one), (sN, .one), (sI, .one)], neFun, .one) := by
    show u.code.lookup fNumEnd = _; rw [c0]; exact hc
  have hne := numEnd_eq hp j (by omega)
  have hnel := numEndL_le b.data.toList j.toNat (by simp; omega)
  have hcall := call3_ret v1 sE2 fNumEnd sB sN sI neFun (vv sB) (vv sN) (vv sI) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 j.toNat) (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b j).toNat) we
    (by decide) (by decide) (by decide) hcode1 (eval_vv v1 sB _ (by lk [v1, v]; exact lb))
    (eval_vv v1 sN _ (by lk [v1, v]; exact ln)) (eval_vv v1 sI _ li1) (by lk [v1, v]; exact le)
    (fun callee h1 h2 h3 => numEnd_refines _ A b hp (bytesAt_congr hb (by exact m0) (by exact d0) (by exact b0))
      j (by omega) (skipDigitsCode_entry callee hc2 (by exact c0)) h1 h2 h3)
  rcases hcall with hs | ⟨w, hw, m1, d1, g1, c1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop v1 _ _ hs)
  rw [seq_normal _ hw]
  obtain ⟨e, he⟩ : ∃ e, e = ConLeche.Frontend.numEnd b j := ⟨_, rfl⟩
  rw [← he] at le1 hstep hne
  have hel : e.toNat ≤ b.size := by rw [hne]; simpa using hnel
  have li2 : w.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact li1
  rw [ite_word w _ _ _ _ (ConsLoop.eval_cmp_of w .equal (vv sE2) (vv sI) _ _ (eval_vv w sE2 _ le1)
    (eval_vv w sI _ li2)), bw_eq _ _ (by omega) (by omega)]
  by_cases hej : e.toNat = j.toNat
  · simp only [bw, hej, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang w)
  simp only [bw, hej, ↓reduceIte, ne_eq, not_true_eq_false]
  have hej' : (e == j) = false := beq_eq_false_iff_ne.mpr (fun h => hej (by rw [h]))
  rw [hej'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  rw [ite_word w _ _ _ _ (eval_lower w (vv sI) (vv sE2) j.toNat e.toNat (by omega) (by omega)
    (eval_vv w sI _ li2) (eval_vv w sE2 _ le1))]
  by_cases hlt0 : ¬ j.toNat < e.toNat
  · simp only [bw, hlt0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang w)
  have hlt2 : j.toNat < e.toNat := by omega
  simp only [bw, hlt2, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  rw [dif_pos (USize.lt_iff_toNat_lt.mpr hlt2)] at hstep
  have lne2 : w.locals.lookup sNe = some (.val (.word (bw (acc ≠ [])))) := by
    rw [lo1 sNe (by decide)]; exact lne1
  rw [seq_normal _ (ConsLoop.assign_local w sNe (.const 1) 1 _ (by simp [evalHOLExact]) lne2)]
  let w1 := setVarHOLFinite sNe (.val (.word 1)) w
  have lw2 : w1.locals.lookup sW = some (.val (.word 1)) := by lk [w1]; rw [lo1 sW (by decide)]; exact lw1
  rw [seq_normal _ (ConsLoop.assign_local w1 sW (.const 0) 0 1 (by simp [evalHOLExact]) lw2)]
  let w2 := setVarHOLFinite sW (.val (.word 0)) w1
  rw [ConsLoop.assign_local w2 sI (vv sE2) (BitVec.ofNat 64 e.toNat) _ (eval_vv w2 sE2 _ (by lk [w2, w1]; exact le1))
    (by lk [w2, w1]; exact li2)]
  refine Or.inr ⟨rfl, frame _ (m1.trans rfl) d1 c1 g1 b1 (by lk [w2, w1]; rw [lo1 sB (by decide)]; lk [v1, v]; exact lb)
    (by lk [w2, w1]; rw [lo1 sN (by decide)]; lk [v1, v]; exact ln)
    ⟨BitVec.ofNat 64 c.toNat, by lk [w2, w1]; rw [lo1 sC (by decide)]; exact lc1⟩
    ⟨_, by lk [w2, w1]; exact le1⟩
    ⟨e, ConLeche.Frontend.readNatAt b j e :: acc, false, hel, by lk, by lk [w2]; rfl,
      by lk [w2, w1]; simp [bw], Or.inl ⟨by lk [w2, w1]; rw [lo1 sG (by decide)]; exact lg1, by rw [← hR, hstep]⟩⟩⟩


theorem nlLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (R : ConLeche.Frontend.ScanRes (List Nat))
    (hb : BytesAt t A b.data.toList) (hc : NumEndCode t) (hc2 : SkipDigitsCode t)
    (u : PanSemStateFiniteExact 64 σ) (hu : NlI t A b R u) :
    Stop (evaluateHOLFiniteState u nlLoop).1 ∨ ((evaluateHOLFiniteState u nlLoop).1 = none ∧
      NlI t A b R (evaluateHOLFiniteState u nlLoop).2 ∧
      (evaluateHOLFiniteState u nlLoop).2.locals.lookup sG = some (.val (.word 0))) := by
  have := while_stop (vv sG) nlBody (NlI t A b R)
    (fun u => NlI t A b R u ∧ u.locals.lookup sG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, _, j, acc, wi, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, _⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        exact nl_step t A b hp R hb hc hc2 u hu hg
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hg⟩, fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- **`scanNatList` in Pancake is sound for con-leche's**: when it returns, con-leche's
`scanNatList` accepts the list at `i`, ending there. -/
theorem nlFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat ≤ b.size)
    (hc : NumEndCode t) (hc2 : SkipDigitsCode t)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t nlFun (fun w => ∃ (e : USize) (xs : List Nat), w = BitVec.ofNat 64 e.toNat ∧ e.toNat ≤ b.size ∧
      ConLeche.Frontend.scanNatList b i = .ok xs e) := by
  have hL : b.size < 2 ^ 64 := hp.size
  unfold nlFun
  refine retP_dec (w := 1) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 1) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t5 := setVarHOLFinite sE2 (.val (.word 0)) (setVarHOLFinite sC (.val (.word 0))
    (setVarHOLFinite sNe (.val (.word 0)) (setVarHOLFinite sW (.val (.word 1))
      (setVarHOLFinite sG (.val (.word 1)) t))))
  have e1 := bAt_spec t5 A b.data.toList sC (vv sI) i.toNat (bytesAt_congr hb rfl rfl rfl) (by omega) 0
    (by lk [t5]) (by lk [t5]; exact lb) (by lk [t5]; simpa using ln) (eval_vv t5 sI _ (by lk [t5]; exact li))
  refine retP_seq e1 ?_ rfl rfl rfl rfl rfl
  let t6 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList i.toNat).toNat))) t5
  have hcmp := eval_eq_c t6 sC (byteL b.data.toList i.toNat).toNat 91
    (by have := UInt8.toNat_lt (byteL b.data.toList i.toNat); omega) (by decide) (by lk [t6])
  simp only [show (91 : BitVec 64) = BitVec.ofNat 64 91 from rfl] at *
  refine retP_ite hcmp (fun hw => ?_) (fun _ => retP_hang _ _)
  have h91 : (byteL b.data.toList i.toNat).toNat = 91 := by
    cases hh : decide ((byteL b.data.toList i.toNat).toNat = 91) <;> simp_all [bw]
  have hi' : i.toNat < b.size := by
    by_cases h : i.toNat < b.size
    · exact h
    · simp [byteL, List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ i.toNat)] at h91
  have hi1 : (i + 1).toNat = i.toNat + 1 := ConLeche.Frontend.usizeStep b i ((hp.lt_iff i).mpr hi')
  have li6 : t6.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))) := by lk [t6, t5]; exact li
  have ei : evaluateHOLFiniteState t6 incI =
      (none, setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (i + 1).toNat))) t6) :=
    ConsLoop.assign_local t6 sI _ _ _ (by
      rw [eval_add_c t6 sI _ _ li6, hi1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega) li6
  refine retP_seq ei ?_ rfl rfl rfl rfl rfl
  let t7 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (i + 1).toNat))) t6
  have h0 : NlI t A b (ConLeche.Frontend.scanNatListLoop b (i + 1) [] true) t7 :=
    ⟨rfl, rfl, rfl, rfl, rfl, by lk [t7, t6, t5]; exact lb, by lk [t7, t6, t5]; exact ln,
      ⟨BitVec.ofNat 64 (byteL b.data.toList i.toNat).toNat, by lk [t7, t6]⟩, ⟨0, by lk [t7, t6, t5]⟩, i + 1, [], true, by omega, by lk [t7], by lk [t7, t6, t5]; rfl,
      by lk [t7, t6, t5]; rfl, Or.inl ⟨by lk [t7, t6, t5], rfl⟩⟩
  rcases nlLoop_spec t A b hp _ hb hc hc2 t7 h0 with hs | ⟨hn, hI, hg⟩
  · exact Or.inl (seq_stop t7 _ _ hs)
  obtain ⟨m0, d0, c0, g0, b0, -, -, -, -, j, acc, wi, hjb, lj, -, -, br⟩ := hI
  have hR := (br.resolve_left (fun ⟨h1, _⟩ => by rw [hg] at h1; cases h1)).2
  generalize hu : evaluateHOLFiniteState t7 nlLoop = r at hn lj m0 d0 c0 g0 b0
  obtain ⟨r1, r2⟩ := r
  simp only at hn lj m0 d0 c0 g0 b0
  subst hn
  refine retP_seq hu ?_ m0 d0 g0 c0 b0
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sI _ lj
  refine Or.inr ⟨_, q1, ⟨j, acc.reverse, rfl, hjb, ?_⟩, q2, q3, q4, q5, q6⟩
  rw [ConLeche.Frontend.scanNatList, byteAt_eq hp]
  have : (b.data.toList[i.toNat]?.getD 0 == 91) = true := by
    rw [show (91 : UInt8) = UInt8.ofNat 91 from rfl, beq_ofNat _ 91 (by decide)]
    simpa [byteL] using h91
  rw [this]; simp only [↓reduceIte]; exact hR

end

end ConPanqueque.Scan
