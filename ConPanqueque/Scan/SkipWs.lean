import ConPanqueque.Scan.Model
import ConPanqueque.Logic.Byte
import ConPanqueque.V.Key

/-! # `skipWs` in Pancake

The first scanner function, and the template for the rest: a `while` over a `go` flag (no
`break`), one `loadByte` per iteration, specified against the list model `skipWsL`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sB := ofString "b"
def sN := ofString "n"
def sI := ofString "i"
def sG := ofString "go"
def sC := ofString "c"

/-- `c == 32 || c == 9 || c == 13`, as a 0/1 word. -/
def wsTest : ExpHOL 64 :=
  .op .or [.cmp .equal (vv sC) (.const 32),
    .op .or [.cmp .equal (vv sC) (.const 9), .cmp .equal (vv sC) (.const 13)]]

def skBody : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite wsTest (.assign .local sI (.op .add [vv sI, .const 1])) (.assign .local sG (.const 0))))
    (.assign .local sG (.const 0))

def skLoop : ProgHOL 64 := .while (vv sG) skBody

section
variable {σ : Type}

theorem eval_wsTest (u : PanSemStateFiniteExact 64 σ) (c : Nat) (hc : c < 256)
    (h : u.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c)))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) wsTest =
      some (.val (.word (bw (isWsN c = true)))) := by
  have e : ∀ k : Nat, k < 256 → (BitVec.ofNat 64 c == BitVec.ofNat 64 k) = (c == k) := by
    intro k hk
    by_cases hck : c = k
    · subst hck; simp
    · have : BitVec.ofNat 64 c ≠ BitVec.ofNat 64 k := by
        intro e; apply hck; have := congrArg BitVec.toNat e; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr hck]
  have e32 : (BitVec.ofNat 64 c == 32#64) = (c == 32) := e 32 (by decide)
  have e9 : (BitVec.ofNat 64 c == 9#64) = (c == 9) := e 9 (by decide)
  have e13 : (BitVec.ofNat 64 c == 13#64) = (c == 13) := e 13 (by decide)
  simp only [wsTest, evalHOLExact, evalListHOLExact, vv, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    e32, e9, e13]
  have f : ∀ k : Nat, k < 256 → (BitVec.ofNat 64 c = BitVec.ofNat 64 k ↔ c = k) := by
    intro k hk
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  have f32 : (BitVec.ofNat 64 c = 32#64) ↔ c = 32 := f 32 (by decide)
  have f9 : (BitVec.ofNat 64 c = 9#64) ↔ c = 9 := f 9 (by decide)
  have f13 : (BitVec.ofNat 64 c = 13#64) ↔ c = 13 := f 13 (by decide)
  by_cases h32 : c = 32 <;> by_cases h9 : c = 9 <;> by_cases h13 : c = 13 <;>
    simp [h32, h9, h13, f32, f9, f13, isWsN, bw, wordOpHOL, wordOp, valueIsWord, valueWord] <;>
    first | decide | omega

theorem bytesAt_congr {t u : PanSemStateFiniteExact 64 σ} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt t a bs) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hb : u.be = t.be) :
    BytesAt u a bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hb]; exact h1, h2, h3, fun i hi => by rw [hm, hd]; exact h4 i hi⟩

theorem skipWsL_step (bs : List UInt8) (j : Nat) (hj : j < bs.length) :
    skipWsL bs j = if isWsN bs[j].toNat then skipWsL bs (j + 1) else j := by
  rw [skipWsL, dif_pos hj]

theorem skipWsL_end (bs : List UInt8) (j : Nat) (hj : ¬ j < bs.length) : skipWsL bs j = j := by
  rw [skipWsL, dif_neg hj]

/-- The loop's invariant: the frame, the buffer's address and length, and the position `j`, from
which skipping gives the same answer as from `i0`, or which is that answer once `go` is `0`. -/
def SkI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) ∧
  (∃ c, u.locals.lookup sC = some (.val (.word c))) ∧
  ∃ j, j ≤ bs.length ∧ u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ skipWsL bs j = skipWsL bs i0) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ j = skipWsL bs i0))

theorem sk_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ) (hu : SkI t A bs i0 u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) skBody = (none, u') ∧ SkI t A bs i0 u' := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, ⟨c, lc⟩, j, hj, li, br⟩ := hu
  obtain ⟨_, hsame⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  let v := decClockHOLFinite u
  have hlt : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.cmp .lower (vv sI) (vv sN)) = some (.val (.word (bw (j < bs.length)))) := by
    rw [ConsLoop.eval_cmp_of v .lower _ _ (BitVec.ofNat 64 j) (BitVec.ofNat 64 bs.length)
      (eval_vv v sI _ (by lk [v]; exact li)) (eval_vv v sN _ (by lk [v]; exact ln))]
    simp only [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have : (BitVec.ofNat 64 j < BitVec.ofNat 64 bs.length) ↔ j < bs.length := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt hL]
    by_cases h : j < bs.length <;> simp [h, this]
  unfold skBody
  rw [ite_word v _ _ _ _ hlt]
  by_cases hjl : j < bs.length
  · simp only [bw, hjl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hbv : BytesAt v A bs := bytesAt_congr hb m0 d0 b0
    have haddr : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
        (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j))) := by
      have lb' : v.locals.lookup sB = some (.val (.word A)) := by lk [v]; exact lb
      have li' : v.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by lk [v]; exact li
      simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [seq_normal _ (ConsLoop.assign_local v sC _ (BitVec.ofNat 64 bs[j].toNat) c
      (eval_loadByte_bytes v _ A bs j hbv hjl haddr) (by lk [v]; exact lc))]
    let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 bs[j].toNat))) v
    have hws := eval_wsTest v1 bs[j].toNat (UInt8.toNat_lt _) (by lk [v1])
    rw [ite_word v1 _ _ _ _ hws]
    by_cases hw : isWsN bs[j].toNat = true
    · simp only [bw, hw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by lk [v1, v]; exact li
      rw [ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1)) _ (by
        rw [eval_add_c v1 sI _ _ li1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li1]
      refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v1, v]; exact lb, by lk [v1, v]; exact ln,
        ⟨BitVec.ofNat 64 bs[j].toNat, by lk [v1, v]⟩, j + 1, hjl, by lk, Or.inl ⟨by lk [v1, v]; exact hg, ?_⟩⟩
      rw [← hsame, skipWsL_step bs j hjl, if_pos hw]
    · simp only [bw, hw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
      rw [ConsLoop.assign_local v1 sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v1, v]; exact hg)]
      refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v1, v]; exact lb, by lk [v1, v]; exact ln,
        ⟨BitVec.ofNat 64 bs[j].toNat, by lk [v1, v]⟩, j, hj, by lk [v1, v]; exact li, Or.inr ⟨by lk, ?_⟩⟩
      rw [← hsame, skipWsL_step bs j hjl, if_neg hw]
  · simp only [bw, hjl, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [ConsLoop.assign_local v sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v]; exact hg)]
    refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v]; exact lb, by lk [v]; exact ln,
      ⟨c, by lk [v]; exact lc⟩, j, hj, by lk [v]; exact li, Or.inr ⟨by lk, ?_⟩⟩
    rw [← hsame, skipWsL_end bs j hjl]

theorem skLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ) (hu : SkI t A bs i0 u) :
    Stop (evaluateHOLFiniteState u skLoop).1 ∨ ((evaluateHOLFiniteState u skLoop).1 = none ∧
      SkI t A bs i0 (evaluateHOLFiniteState u skLoop).2 ∧
      (evaluateHOLFiniteState u skLoop).2.locals.lookup sI =
        some (.val (.word (BitVec.ofNat 64 (skipWsL bs i0))))) := by
  have := while_stop (vv sG) skBody (SkI t A bs i0)
    (fun u => SkI t A bs i0 u ∧ u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 (skipWsL bs i0)))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, j, _, li, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hj⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := sk_step t A bs i0 hb u hu hg
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, by rw [li, hj]⟩,
          fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- `skipWs(b, n, i)`: the first non-whitespace position at or after `i` in the `n` bytes at `b`. -/
def skFun : ProgHOL 64 :=
  .dec sG .one (.const 1) (.dec sC .one (.const 0) (.seq skLoop (.return (vv sI))))

/-- **`skipWs` refines its list model**: started with the buffer's address, its length and a
position at most the length, the function stops or returns the model's answer, and the memory,
its domain, the globals and the code are as they were. -/
theorem skFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (hi : i0 ≤ bs.length)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    Stop (evaluateHOLFiniteState t skFun).1 ∨
      ((evaluateHOLFiniteState t skFun).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (skipWsL bs i0))))) ∧
        (evaluateHOLFiniteState t skFun).2.memory = t.memory ∧
        (evaluateHOLFiniteState t skFun).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t skFun).2.globals = t.globals ∧
        (evaluateHOLFiniteState t skFun).2.code = t.code) := by
  unfold skFun
  rw [dec_word_eq t sG _ 1 _ (by simp [evalHOLExact])]
  let t1 := setVarHOLFinite sG (.val (.word 1)) t
  rw [dec_word_eq t1 sC _ 0 _ (by simp [evalHOLExact])]
  let t2 := setVarHOLFinite sC (.val (.word 0)) t1
  have h0 : SkI t A bs i0 t2 := ⟨rfl, rfl, rfl, rfl, rfl, by lk [t2, t1]; exact lb, by lk [t2, t1]; exact ln,
    ⟨0, by lk [t2]⟩, i0, hi, by lk [t2, t1]; exact li, Or.inl ⟨by lk [t2, t1], rfl⟩⟩
  rcases skLoop_spec t A bs i0 hb t2 h0 with hs | ⟨hn, hI, hres⟩
  · exact Or.inl (seq_stop t2 skLoop _ hs)
  · right
    obtain ⟨m0, d0, c0, g0, -, -⟩ := hI
    generalize hu : evaluateHOLFiniteState t2 skLoop = r at hn hres m0 d0 c0 g0
    obtain ⟨r1, r2⟩ := r
    simp only at hn hres m0 d0 c0 g0
    subst hn
    rw [seq_normal _ hu, evaluateHOLFiniteState_eq_evaluate_def r2 (.return _)]
    simp [eval_vv r2 sI _ hres, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
      emptyLocalsHOLFinite, m0, d0, c0, g0]

/-- **`skipWs` in Pancake is con-leche's `skipWs`**: on a buffer holding the bytes of `b`. -/
theorem skFun_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    Stop (evaluateHOLFiniteState t skFun).1 ∨
      ((evaluateHOLFiniteState t skFun).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (ConLeche.Frontend.skipWs b i).toNat)))) ∧
        (evaluateHOLFiniteState t skFun).2.memory = t.memory ∧
        (evaluateHOLFiniteState t skFun).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t skFun).2.globals = t.globals ∧
        (evaluateHOLFiniteState t skFun).2.code = t.code) := by
  rw [skipWs_eq hp _ i rfl]
  exact skFun_spec t A b.data.toList i.toNat hb (by simpa using hi) lb (by simpa using ln) li

end

end ConPanqueque.Scan
