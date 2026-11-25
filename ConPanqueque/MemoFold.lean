import ConPanqueque.ExprFold
import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Fold ConPanqueque.Table ConPanqueque.ExprFold

/-!
# Memoized folds over expressions

con-leche's expressions are DAGs, so its kernel memoizes its walks. `memoBody fr`
looks the node pointer up in a table (globals `tbl`, `tlim`); on a miss it calls
`fr` (the raw fold, whose recursive calls come back here), inserts the result and
returns it. `MemoInv` is the invariant: table and arena are disjoint parts of
memory, and every entry stores `f` of the expression at its key (well defined by
`exprAt_unique`). `memo_node`: one node of the memoized fold is correct under
the invariant.
-/

namespace ConPanqueque.MemoFold

def nTbl := ofString "tbl"
def nTlim := ofString "tlim"

/-- The memoized function: look `u` up; on a miss call `fr` (the raw fold, whose
recursive calls go to this function), insert the result, return it. -/
def memoBody (fr : MlS) : ProgHOL 64 :=
  .dec nT .one (.var .global nTbl)
  (.dec nK .one (.var .local nU)
  (.dec nL .one (.var .global nTlim)
  (.dec nJ .one (.const 0)
  (.dec nR .one (.const 0)
  (.dec nG .one (.const 1)
  (.seq scanLoop
    (.ite (.cmp .equal (vv nJ) (vv nL))
      (.dec nV .one (.const 0)
        (.seq (.call (some (some (.local, nV), none)) fr [.var .local nU])
          (.seq (.assign .local nJ (.const 0))
            (.seq (.assign .local nG (.const 1))
              (.dec nO .one (.const 0)
                (.seq insLoop (.return (vv nV))))))))
      (.return (vv nR)))))))))

/-- The memo invariant: the table (at `tb`, `n` slots) and the arena are disjoint parts
of memory, and every entry stores `f` of the expression at its key. -/
def MemoInv {σ : Type} (h : Heap) (f : ConLeche.Expr → UInt64) (tb : BitVec 64) (n : Nat)
    (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.globals.lookup nTbl = some (.val (.word tb)) ∧
  t.globals.lookup nTlim = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
  ∃ slots : List (BitVec 64 × BitVec 64), slots.length = n ∧ Sat t (TableAt tb slots ∗ (· = h)) ∧
    ∀ kv ∈ slots, kv.1 ≠ 0 → ∃ e, ExprAt h kv.1 e ∧ kv.2 = (f e).toBitVec

theorem memoInv_inMem {σ : Type} {h : Heap} {f : ConLeche.Expr → UInt64} {tb : BitVec 64} {n : Nat}
    {t : PanSemStateFiniteExact 64 σ} (hj : MemoInv h f tb n t) : InMem t h := by
  obtain ⟨_, _, slots, _, ⟨hh, ⟨h1, h2, hd, he, _, rfl⟩, hm⟩, _⟩ := hj
  intro a w ha
  apply hm a w
  subst he
  rcases hd a with e1 | e2
  · simp [union, e1, ha]
  · rw [e2] at ha; cases ha

theorem memoInv_memDet {σ : Type} (h : Heap) (f : ConLeche.Expr → UInt64) (tb : BitVec 64) (n : Nat) :
    MemDet (MemoInv (σ := σ) h f tb n) := by
  intro t t' hm hd hg ⟨g1, g2, slots, hl, hs, hc⟩
  refine ⟨by rw [hg]; exact g1, by rw [hg]; exact g2, slots, hl, ?_, hc⟩
  obtain ⟨hh, hp, hhm⟩ := hs
  exact ⟨hh, hp, fun a w ha => by rw [hm, hd]; exact hhm a w ha⟩

end ConPanqueque.MemoFold

namespace ConPanqueque.Table

theorem insSlots_mem (k v : BitVec 64) : ∀ (slots sl' : List (BitVec 64 × BitVec 64)),
    insSlots k v slots = some sl' → ∀ kv ∈ sl', kv ∈ slots ∨ kv = (k, v)
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, sl', h => by
    simp only [insSlots] at h
    split at h
    · cases h; intro kv hkv; simp at hkv
      rcases hkv with rfl | hkv
      · right; rfl
      · left; simp [hkv]
    · cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r =>
        simp [e] at h; subst h
        intro kv hkv; simp at hkv
        rcases hkv with rfl | hkv
        · left; simp
        · rcases insSlots_mem k v rest r e kv hkv with h1 | h1
          · left; simp [h1]
          · right; exact h1

end ConPanqueque.Table

namespace ConPanqueque.MemoFold

/-- One node of the memoized fold: if the raw computation on node `p` returns
`f e` under the memo invariant, the memoized function does too (a hit returns the
stored value, a miss computes, inserts and returns). -/
def memoCost (n craw : Nat) : Nat := (n + 1) + 1 + craw + (n + 1)

theorem memo_node {σ : Type} (fm fr : MlS) (Braw : ProgHOL 64) (h : Heap) (f : ConLeche.Expr → UInt64)
    (tb : BitVec 64) (n : Nat) (hn : 16 * n < 2 ^ 64) (p : BitVec 64) (e : ConLeche.Expr) (he : ExprAt h p e)
    (craw : Nat)
    (s : PanSemStateFiniteExact 64 σ)
    (hraw : ∀ t : PanSemStateFiniteExact 64 σ, t.code = s.code →
      MemoInv h f tb n t → t.locals.lookup nU = some (.val (.word p)) → craw ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t Braw = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
        PostJ (MemoInv h f tb n) t st craw)
    (hcr : s.code.lookup fr = some ([(nU, .one)], Braw, .one))
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
    rw [ite_eq_left (by decide : (1 : BitVec 64) ≠ 0)]
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
          (by simp [callEntryStateHOLFinite, c8])
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

/-! ## The memoized fold -/

/-- One node of the memoized fold, given its raw case (children, result expression). -/
theorem memo_case {σ : Type} (fm fr : MlS) (g : Fin 10 → ExpHOL 64) (h : Heap) (f : ConLeche.Expr → UInt64)
    (tb : BitVec 64) (n : Nat) (hn : 16 * n < 2 ^ 64)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hCm : C.lookup fm = some ([(nU, .one)], memoBody fr, .one))
    (hCr : C.lookup fr = some ([(nU, .one)], ExprFold.body fm g, .one))
    (p c : BitVec 64) (e : ConLeche.Expr) (he : ExprAt h p e) (h0 : h p = some (.word c))
    (ks : List Kid) (gc : ExpHOL 64)
    (hpick : pick c (cases fm g) (.return (.const 0)) = callKids fm (ks.map fun k => (k.x, k.off)) (.return gc))
    (hnd : (ks.map Kid.x).Nodup) (hnu : nU ∉ ks.map Kid.x) (htg : nTg ∉ ks.map Kid.x)
    (hkids : ∀ k ∈ ks, h (p + k.off) = some (.word k.q) ∧
        ∀ t' : PanSemStateFiniteExact 64 σ, t'.code = C → MemoInv h f tb n t' →
          t'.locals.lookup nU = some (.val (.word k.q)) → k.c ≤ t'.clock →
          ∃ st, evaluateHOLFiniteState t' (memoBody fr) = (some (.returned (.val (.word k.r.toBitVec))), st) ∧
            PostJ (MemoInv h f tb n) t' st k.c)
    (hg : ∀ t' : PanSemStateFiniteExact 64 σ, (∀ k ∈ ks, t'.locals.lookup k.x = some (.val (.word k.r.toBitVec))) →
      @evalHOLExact 64 σ _ t'.toExact (fun x => Classical.propDecidable (t'.memaddrs x)) gc =
        some (.val (.word (f e).toBitVec)))
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code = C) (hj : MemoInv h f tb n s)
    (hu : s.locals.lookup nU = some (.val (.word p))) (hck : memoCost n (kidsCost ks) ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (memoBody fr) = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
      PostJ (MemoInv h f tb n) s st (memoCost n (kidsCost ks)) :=
  memo_node fm fr (ExprFold.body fm g) h f tb n hn p e he (kidsCost ks) s
    (fun t ht hj' hu' hck' => fold_caseJ fm (memoBody fr) g h p c (MemoInv h f tb n) (fun t ht => memoInv_inMem ht)
      (memoInv_memDet h f tb n) C hCm ks gc (f e) hpick hnd hnu htg hkids hg t (ht.trans hc) hj' hu' h0 hck')
    (by rw [hc]; exact hCr) hj hu hck

/-- Clock used by the memoized fold (worst case: every node misses). -/
def mcost (n : Nat) : ConLeche.Expr → Nat
  | .bvar _ | .sort _ | .const _ _ | .lit _ => memoCost n 0
  | .fvar _ ty | .proj _ _ ty => memoCost n (1 + mcost n ty)
  | .app a b | .lam a b | .forallE a b => memoCost n (1 + mcost n a + (1 + mcost n b))
  | .letE a b c => memoCost n (1 + mcost n a + (1 + mcost n b + (1 + mcost n c)))

/-- The memoized expression fold computes `f`, and keeps the table invariant. -/
theorem memo_fold_spec {σ : Type} (fm fr : MlS) (g : Fin 10 → ExpHOL 64) (f : ConLeche.Expr → UInt64)
    (sp : ExprFoldSpec g f) (h : Heap) (tb : BitVec 64) (n : Nat) (hn : 16 * n < 2 ^ 64)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hCm : C.lookup fm = some ([(nU, .one)], memoBody fr, .one))
    (hCr : C.lookup fr = some ([(nU, .one)], ExprFold.body fm g, .one))
    {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    ∀ s : PanSemStateFiniteExact 64 σ, s.code = C → MemoInv h f tb n s →
      s.locals.lookup nU = some (.val (.word p)) → mcost n e ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s (memoBody fr) = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
        PostJ (MemoInv h f tb n) s st (mcost n e) := by
  induction he with
  | bvar hp h0 hd h2 hi =>
    intro s hc hj hu hck
    exact memo_case fm fr g h f tb n hn C hCm hCr _ 0 _ (.bvar hp h0 hd h2 hi) h0 [] (g 0) rfl (by simp) (by simp) (by simp)
      (by simp) (fun t _ => sp.bvar t _) s hc hj hu (by simpa [kidsCost, mcost] using hck)
  | @fvar p v q i ty hp h0 hd h2 h3 hi hty ih =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 1 _ (.fvar hp h0 hd h2 h3 hi hty) h0
      [⟨nA, 24, q, f ty, mcost n ty⟩] (g 1) rfl (by simp) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨h3, ih⟩) (fun t hk => sp.fvar t i ty (by simp at hk; exact hk)) s hc hj hu
      (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this
  | sort hp h0 hd h2 hu' =>
    intro s hc hj hu hck
    exact memo_case fm fr g h f tb n hn C hCm hCr _ 2 _ (.sort hp h0 hd h2 hu') h0 [] (g 2) rfl (by simp) (by simp) (by simp)
      (by simp) (fun t _ => sp.sort t _) s hc hj hu (by simpa [kidsCost, mcost] using hck)
  | const hp h0 hd h2 h3 hn' hus =>
    intro s hc hj hu hck
    exact memo_case fm fr g h f tb n hn C hCm hCr _ 3 _ (.const hp h0 hd h2 h3 hn' hus) h0 [] (g 3) rfl (by simp) (by simp)
      (by simp) (by simp) (fun t _ => sp.const t _ _) s hc hj hu (by simpa [kidsCost, mcost] using hck)
  | @app p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 4 _ (.app hp h0 hd h2 h3 ha hb) h0
      [⟨nA, 16, q, f a, mcost n a⟩, ⟨nB, 24, r, f b, mcost n b⟩] (g 4) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.app t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hj hu (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this
  | @lam p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 5 _ (.lam hp h0 hd h2 h3 ha hb) h0
      [⟨nA, 16, q, f a, mcost n a⟩, ⟨nB, 24, r, f b, mcost n b⟩] (g 5) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.lam t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hj hu (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this
  | @forallE p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 6 _ (.forallE hp h0 hd h2 h3 ha hb) h0
      [⟨nA, 16, q, f a, mcost n a⟩, ⟨nB, 24, r, f b, mcost n b⟩] (g 6) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.forallE t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hj hu (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this
  | @letE p q r w a b c hp h0 hd h2 h3 h4 ha hb hc' iha ihb ihc =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 7 _ (.letE hp h0 hd h2 h3 h4 ha hb hc') h0
      [⟨nA, 16, q, f a, mcost n a⟩, ⟨nB, 24, r, f b, mcost n b⟩, ⟨nC, 32, w, f c, mcost n c⟩] (g 7) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩, ⟨h4, ihc⟩⟩)
      (fun t hk => sp.letE t a b c (by simp at hk; exact hk.1) (by simp at hk; exact hk.2.1) (by simp at hk; exact hk.2.2))
      s hc hj hu (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this
  | lit hp h0 hd h2 hl =>
    intro s hc hj hu hck
    exact memo_case fm fr g h f tb n hn C hCm hCr _ 8 _ (.lit hp h0 hd h2 hl) h0 [] (g 8) rfl (by simp) (by simp) (by simp)
      (by simp) (fun t _ => sp.lit t _) s hc hj hu (by simpa [kidsCost, mcost] using hck)
  | @proj p q v r n' i e hp h0 hd h2 h3 h4 hn' hi he ih =>
    intro s hc hj hu hck
    have := memo_case fm fr g h f tb n hn C hCm hCr p 9 _ (.proj hp h0 hd h2 h3 h4 hn' hi he) h0
      [⟨nA, 32, r, f e, mcost n e⟩] (g 9) rfl (by simp) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide) (by simpa using ⟨h4, ih⟩)
      (fun t hk => sp.proj t n' i e (by simp at hk; exact hk)) s hc hj hu (by simpa [kidsCost, mcost] using hck)
    simpa [kidsCost, mcost] using this

end ConPanqueque.MemoFold
