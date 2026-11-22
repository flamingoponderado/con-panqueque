import ConPanqueque.MemoFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Fold ConPanqueque.Table

namespace ConPanqueque.MemoFold

def memoCost (n craw : Nat) : Nat := (n + 1) + 1 + craw + (n + 1)

theorem memo_node {σ : Type} (fm fr : MlS) (Braw : ProgHOL 64) (h : Heap) (f : ConLeche.Expr → UInt64)
    (tb : BitVec 64) (n : Nat) (hn : 16 * n < 2 ^ 64) (p : BitVec 64) (e : ConLeche.Expr) (he : ExprAt h p e)
    (craw : Nat)
    (hraw : ∀ t : PanSemStateFiniteExact 64 σ, t.code.lookup fr = some ([(nU, .one)], Braw, .one) →
      MemoInv h f tb n t → t.locals.lookup nU = some (.val (.word p)) → craw ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t Braw = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
        PostJ (MemoInv h f tb n) t st craw)
    (s : PanSemStateFiniteExact 64 σ) (hcr : s.code.lookup fr = some ([(nU, .one)], Braw, .one))
    (hj : MemoInv h f tb n s) (hu : s.locals.lookup nU = some (.val (.word p)))
    (hck : memoCost n craw ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (memoBody fr) = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
      PostJ (MemoInv h f tb n) s st (memoCost n craw) := by
  obtain ⟨g1, g2, slots, hlen, hsat, hent⟩ := hj
  have hjd := memoInv_memDet (σ := σ) h f tb n
  have hp0 : p ≠ 0 := (exprAt_data he).1
  -- the six declarations
  let s1 := setVarHOLFinite nT (.val (.word tb)) s
  let s2 := setVarHOLFinite nK (.val (.word p)) s1
  let s3 := setVarHOLFinite nL (.val (.word (BitVec.ofNat 64 (16 * n)))) s2
  let s4 := setVarHOLFinite nJ (.val (.word 0)) s3
  let s5 := setVarHOLFinite nR (.val (.word 0)) s4
  let s6 := setVarHOLFinite nG (.val (.word 1)) s5
  have dist : nT ≠ nK ∧ nT ≠ nL ∧ nT ≠ nJ ∧ nT ≠ nR ∧ nT ≠ nG ∧ nK ≠ nL ∧ nK ≠ nJ ∧ nK ≠ nR ∧ nK ≠ nG ∧
      nL ≠ nJ ∧ nL ≠ nR ∧ nL ≠ nG ∧ nJ ≠ nR ∧ nJ ≠ nG ∧ nR ≠ nG ∧ nU ≠ nT ∧ nU ≠ nK ∧ nU ≠ nL ∧ nU ≠ nJ ∧
      nU ≠ nR ∧ nU ≠ nG := by decide
  have l6 : ∀ x y, (x = nT ∧ y = .val (.word tb)) ∨ (x = nK ∧ y = .val (.word p)) ∨
      (x = nL ∧ y = .val (.word (BitVec.ofNat 64 (16 * n)))) ∨ (x = nJ ∧ y = .val (.word 0)) ∨
      (x = nR ∧ y = .val (.word 0)) ∨ (x = nG ∧ y = .val (.word 1)) → s6.locals.lookup x = some y := by
    intro x y hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (config := { decide := true }) [s6, s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE, nT, nK, nL, nJ, nR, nG]
  have m6 : s6.memory = s.memory ∧ s6.memaddrs = s.memaddrs ∧ s6.globals = s.globals ∧ s6.clock = s.clock ∧
      s6.code = s.code := by simp [s6, s5, s4, s3, s2, s1, setVarHOLFinite]
  have hsat6 : Sat s6 (TableAt tb slots ∗ (· = h)) := sat_of_eq m6.1 m6.2.1 hsat
  obtain ⟨s7, ev7, r7, mem7, md7, fr7, g7, i7, hi7, j7, iff7, clk7⟩ := scanLoop_spec s6 tb p slots (· = h) (by rw [hlen]; exact hn)
    hsat6 (l6 _ _ (by simp)) (l6 _ _ (by simp)) (by rw [hlen]; exact l6 _ _ (by simp)) (l6 _ _ (by simp))
    (l6 _ _ (by simp)) (l6 _ _ (by simp)) (by rw [hlen, m6.2.2.2.1]; unfold memoCost at hck; omega)
  have hU6 : s6.locals.lookup nU = some (.val (.word p)) := by
    simp (config := { decide := true }) [s6, s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE, nT, nK, nL, nJ, nR, nG, nU]
    exact hu
  have lL7 : s7.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * n)))) := by
    rw [fr7.2.2 nL (by decide)]; exact l6 _ _ (by simp)
  have lJ7 := j7
  rw [hlen] at hi7 iff7
  -- pass the six declarations
  obtain ⟨L1, d1⟩ := dec_word' s nT (.var .global nTbl) tb _ (by simp [evalHOLExact, g1])
  obtain ⟨L2, d2⟩ := dec_word' s1 nK (.var .local nU) p _ (by simp [evalHOLExact, s1, setVarHOLFinite, FUPDATE,
    show nT ≠ nU from by decide, hu])
  obtain ⟨L3, d3⟩ := dec_word' s2 nL (.var .global nTlim) (BitVec.ofNat 64 (16 * n)) _ (by
    simp [evalHOLExact, s2, s1, setVarHOLFinite, g2])
  obtain ⟨L4, d4⟩ := dec_word' s3 nJ (.const 0) 0 _ (by simp [evalHOLExact])
  obtain ⟨L5, d5⟩ := dec_word' s4 nR (.const 0) 0 _ (by simp [evalHOLExact])
  obtain ⟨L6, d6⟩ := dec_word' s5 nG (.const 1) 1 _ (by simp [evalHOLExact])
  unfold memoBody
  rw [d1, show setVarHOLFinite nT (.val (.word tb)) s = s1 from rfl, d2,
    show setVarHOLFinite nK (.val (.word p)) s1 = s2 from rfl, d3,
    show setVarHOLFinite nL (.val (.word (BitVec.ofNat 64 (16 * n)))) s2 = s3 from rfl, d4,
    show setVarHOLFinite nJ (.val (.word 0)) s3 = s4 from rfl, d5,
    show setVarHOLFinite nR (.val (.word 0)) s4 = s5 from rfl, d6,
    show setVarHOLFinite nG (.val (.word 1)) s5 = s6 from rfl, seq_normal _ ev7]
  by_cases hit : i7 = n
  · -- not found: compute, insert, return
    subst hit
    rw [ite_word s7 _ _ _ 1 (by simp [evalHOLExact, vv, lJ7, lL7, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    have lU7 : s7.locals.lookup nU = some (.val (.word p)) := by rw [fr7.2.2 nU (by decide)]; exact hU6
    have jd7 : MemoInv h f tb i7 s7 := hjd s s7 (by rw [mem7, m6.1]) (by rw [md7, m6.2.1]) (by rw [fr7.2.1, m6.2.2.1])
      ⟨g1, g2, slots, hlen, hsat, hent⟩
    obtain ⟨L8, d8⟩ := dec_word' s7 nV (.const 0) 0 _ (by simp [evalHOLExact])
    let s8 := setVarHOLFinite nV (.val (.word 0)) s7
    have lU8 : s8.locals.lookup nU = some (.val (.word p)) := by
      simp only [s8]; rw [lookup_setVar_other _ _ (by decide)]; exact lU7
    have c8 : s8.code = s.code := by simp [s8, setVarHOLFinite, fr7.1, m6.2.2.2.2]
    have ck7 : 1 + craw + (i7 + 1) + 1 ≤ s7.clock + 1 := by
      unfold memoCost at hck; rw [m6.2.2.2.1] at clk7; omega
    have ck8 : s8.clock = s7.clock := by simp [s8, setVarHOLFinite]
    obtain ⟨st, ⟨qc, qd, qj, qclk⟩, hcall⟩ := call1 s8 fr nU nV Braw (.var .local nU) p (f e).toBitVec
      (fun st => st.code = s.code ∧ st.memaddrs = s.memaddrs ∧ MemoInv h f tb i7 st ∧ s7.clock - 1 ≤ st.clock + craw)
      (by rw [c8]; exact hcr) (by simp [evalHOLExact, lU8]) (by rw [ck8]; omega) ⟨0, by simp [s8]⟩
      (fun callee hcl => by
        obtain ⟨st, ev, a1, a2, a3, a4⟩ := hraw (callEntryStateHOLFinite s8 callee)
          (by simpa [callEntryStateHOLFinite, c8] using hcr)
          (hjd s7 _ (by simp [callEntryStateHOLFinite, s8, setVarHOLFinite]) (by simp [callEntryStateHOLFinite, s8,
            setVarHOLFinite]) (by simp [callEntryStateHOLFinite, s8, setVarHOLFinite]) jd7)
          (by simpa [callEntryStateHOLFinite] using hcl)
          (by simp only [callEntryStateHOLFinite]; rw [ck8]; omega)
        exact ⟨st, ev, by simpa [callEntryStateHOLFinite, c8] using a1,
          by simpa [callEntryStateHOLFinite, s8, setVarHOLFinite, md7, m6.2.1] using a2, a3,
          by simpa [callEntryStateHOLFinite, s8, setVarHOLFinite] using a4⟩)
    let s9 := setKvarHOLFinite .local nV (.val (.word (f e).toBitVec)) { st with locals := s8.locals }
    have lv9 : ∀ x, x ≠ nV → s9.locals.lookup x = s7.locals.lookup x := by
      intro x hx; simp only [s9, setKvarHOLFinite]; rw [lookup_setVar_other _ _ hx]
      simp only [s8]; rw [lookup_setVar_other _ _ hx]
    have lJ9 : s9.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i7)))) := by
      rw [lv9 _ (by decide)]; exact lJ7
    let s10 := setKvarHOLFinite .local nJ (.val (.word 0)) s9
    have e10 : evaluateHOLFiniteState s9 (.assign .local nJ (.const 0)) = (none, s10) :=
      assign_ok s9 .local nJ _ _ (by simp [evalHOLExact])
        (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lJ9, shapeOfHOLExact, shapeEqHOL])
    have lG10 : s10.locals.lookup nG = some (.val (.word 0)) := by
      simp only [s10, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (by decide), lv9 _ (by decide)]; exact g7
    let s11 := setKvarHOLFinite .local nG (.val (.word 1)) s10
    have e11 : evaluateHOLFiniteState s10 (.assign .local nG (.const 1)) = (none, s11) :=
      assign_ok s10 .local nG _ _ (by simp [evalHOLExact])
        (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lG10, shapeOfHOLExact, shapeEqHOL])
    obtain ⟨L12, d12⟩ := dec_word' s11 nO (.const 0) 0 (.seq insLoop (.return (vv nV))) (by simp [evalHOLExact])
    let s12 := setVarHOLFinite nO (.val (.word 0)) s11
    have l12 : ∀ x, x ≠ nO → x ≠ nG → x ≠ nJ → s12.locals.lookup x = s9.locals.lookup x := by
      intro x h1 h2 h3; simp only [s12, s11, s10, setKvarHOLFinite]
      rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3]
    have st12 : s12.memory = st.memory ∧ s12.memaddrs = st.memaddrs ∧ s12.globals = st.globals ∧
        s12.clock = st.clock ∧ s12.code = st.code := by
      simp [s12, s11, s10, s9, setKvarHOLFinite, setVarHOLFinite]
    obtain ⟨qg1, qg2, slots1, hlen1, hsat1, hent1⟩ := qj
    have hsat12 : Sat s12 (TableAt tb slots1 ∗ (· = h)) := sat_of_eq st12.1 st12.2.1 hsat1
    have s7l : ∀ x y, (x = nT ∧ y = .val (.word tb)) ∨ (x = nK ∧ y = .val (.word p)) ∨
        (x = nL ∧ y = .val (.word (BitVec.ofNat 64 (16 * i7)))) → s12.locals.lookup x = some y := by
      intro x y hxy
      have hx : x ≠ nO ∧ x ≠ nG ∧ x ≠ nJ ∧ x ≠ nV ∧ x ≠ nR := by
        rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      rw [l12 _ hx.1 hx.2.1 hx.2.2.1, lv9 _ hx.2.2.2.1, fr7.2.2 x (by simp [hx.2.2.2.2, hx.2.1, hx.2.2.1])]
      exact l6 x y (by rcases hxy with h | h | h <;> simp [h])
    obtain ⟨s13, ev13, md13, clk13, fr13, res13⟩ := insLoop_spec s12 tb p (f e).toBitVec slots1 (· = h)
      (by rw [hlen1]; exact hn) hsat12 (s7l _ _ (by simp)) (s7l _ _ (by simp))
      (by rw [l12 _ (by decide) (by decide) (by decide)]; simp [s9, setKvarHOLFinite])
      (by rw [hlen1]; exact s7l _ _ (by simp))
      (by simp only [s12]; rw [lookup_setVar_other _ _ (by decide)]; simp only [s11, setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (by decide)]; simp [s10, setKvarHOLFinite])
      (by simp [s12])
      (by simp only [s12]; rw [lookup_setVar_other _ _ (by decide)]; simp [s11, setKvarHOLFinite])
      (by rw [hlen1, st12.2.2.2.1]; omega)
    have lv13 : s13.locals.lookup nV = some (.val (.word (f e).toBitVec)) := by
      rw [fr13.2.2 nV (by decide), l12 _ (by decide) (by decide) (by decide)]; simp [s9, setKvarHOLFinite]
    have eret : evaluateHOLFiniteState s13 (.return (vv nV)) =
        (some (.returned (.val (.word (f e).toBitVec))), emptyLocalsHOLFinite s13) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vv, lv13, shapeOfHOLExact]
    rw [d8, show setVarHOLFinite nV (.val (.word 0)) s7 = s8 from rfl, seq_normal _ hcall,
      show setKvarHOLFinite .local nV (.val (.word (f e).toBitVec)) { st with locals := s8.locals } = s9 from rfl,
      seq_normal _ e10, seq_normal _ e11, d12, show setVarHOLFinite nO (.val (.word 0)) s11 = s12 from rfl,
      seq_normal _ ev13, eret]
    have hinv13 : MemoInv h f tb i7 s13 := by
      rcases res13 with ⟨_, sl', hins, hsat'⟩ | ⟨_, _, hmem⟩
      · refine ⟨by rw [fr13.2.1, st12.2.2.1]; exact qg1, by rw [fr13.2.1, st12.2.2.1]; exact qg2, sl',
          by rw [insSlots_length _ _ _ _ hins, hlen1], hsat', fun kv hkv hk0 => ?_⟩
        rcases insSlots_mem _ _ _ _ hins kv hkv with hold | rfl
        · exact hent1 kv hold hk0
        · exact ⟨e, he, rfl⟩
      · exact hjd st s13 (by rw [hmem, st12.1]) (by rw [md13, st12.2.1]) (by rw [fr13.2.1, st12.2.2.1])
          ⟨qg1, qg2, slots1, hlen1, hsat1, hent1⟩
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [emptyLocalsHOLFinite, fr13.1, st12.2.2.2.2, qc]
    · simp [emptyLocalsHOLFinite, md13, st12.2.1, qd]
    · exact hjd s13 _ (by simp [emptyLocalsHOLFinite]) (by simp [emptyLocalsHOLFinite]) (by simp [emptyLocalsHOLFinite])
        hinv13
    · simp [emptyLocalsHOLFinite]; unfold memoCost; rw [st12.2.2.2.1] at clk13; rw [m6.2.2.2.1] at clk7; omega
  · -- found: return the stored value
    have hne : ¬ (BitVec.ofNat 64 (16 * i7) = BitVec.ofNat 64 (16 * n)) := by
      intro e'; have := congrArg BitVec.toNat e'; simp at this; omega
    rw [ite_word s7 _ _ _ 0 (by simp [evalHOLExact, vv, lJ7, lL7, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    obtain ⟨v, hv⟩ : ∃ v, find? slots p = some v := by
      cases e' : find? slots p with
      | none => exact absurd (iff7.mp (by simp [e'])) hit
      | some v => exact ⟨v, rfl⟩
    obtain ⟨e', he', hval⟩ := hent (p, v) (find?_mem p v slots hv) hp0
    have hee : e' = e := exprAt_unique he' he
    subst hee
    have r7' : s7.locals.lookup nR = some (.val (.word (f e').toBitVec)) := by rw [r7, hv]; simp; exact hval
    have eret : evaluateHOLFiniteState s7 (.return (vv nR)) =
        (some (.returned (.val (.word (f e').toBitVec))), emptyLocalsHOLFinite s7) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vv, r7', shapeOfHOLExact]
    rw [eret]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [emptyLocalsHOLFinite, fr7.1, m6.2.2.2.2]
    · simp [emptyLocalsHOLFinite, md7, m6.2.1]
    · apply hjd s _ (by simp [emptyLocalsHOLFinite, mem7, m6.1]) (by simp [emptyLocalsHOLFinite, md7, m6.2.1])
        (by simp [emptyLocalsHOLFinite, fr7.2.1, m6.2.2.1])
      exact ⟨g1, g2, slots, hlen, hsat, hent⟩
    · simp [emptyLocalsHOLFinite]; unfold memoCost; rw [m6.2.2.2.1] at clk7; omega

end ConPanqueque.MemoFold
