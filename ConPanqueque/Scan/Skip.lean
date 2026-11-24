import ConPanqueque.Scan.Model
import ConPanqueque.Logic.Byte
import ConPanqueque.V.Key

/-! # Skip loops in Pancake

`skip p (b, n, i)`: the first position at or after `i` whose byte fails the test `p`, in the `n`
bytes at `b`.  One loop for every such scanner (`skipWs`, `skipDigits`, …): a `while` over a `go`
flag, one `loadByte` per iteration, the test an expression `T` that computes `p` of the byte in
local `c` (`TestOK`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sB := ofString "b"
def sN := ofString "n"
def sI := ofString "i"
def sG := ofString "go"
def sC := ofString "c"

/-- `T` computes `p` of the byte in `c`, as a 0/1 word. -/
def TestOK (p : Nat → Bool) (T : ExpHOL 64) : Prop :=
  ∀ {σ : Type} (u : PanSemStateFiniteExact 64 σ) (c : Nat), c < 256 →
    u.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c))) →
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) T =
      some (.val (.word (bw (p c = true))))

def skBody (T : ExpHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite T (.assign .local sI (.op .add [vv sI, .const 1])) (.assign .local sG (.const 0))))
    (.assign .local sG (.const 0))

def skLoop (T : ExpHOL 64) : ProgHOL 64 := .while (vv sG) (skBody T)

/-- `skip(b, n, i)`. -/
def skFun (T : ExpHOL 64) : ProgHOL 64 :=
  .dec sG .one (.const 1) (.dec sC .one (.const 0) (.seq (skLoop T) (.return (vv sI))))

section
variable {σ : Type}

theorem bytesAt_congr {t u : PanSemStateFiniteExact 64 σ} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt t a bs) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) (hb : u.be = t.be) :
    BytesAt u a bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hb]; exact h1, h2, h3, fun i hi => by rw [hm, hd]; exact h4 i hi⟩

/-- The loop's invariant: the frame, the buffer's address and length, and the position `j`, from
which skipping gives the same answer as from `i0`, or which is that answer once `go` is `0`. -/
def SkI (p : Nat → Bool) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) ∧
  (∃ c, u.locals.lookup sC = some (.val (.word c))) ∧
  ∃ j, j ≤ bs.length ∧ u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ skipL p bs j = skipL p bs i0) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ j = skipL p bs i0))

theorem sk_step (p : Nat → Bool) (T : ExpHOL 64) (hT : TestOK p T) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ) (hu : SkI p t A bs i0 u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) (skBody T) = (none, u') ∧ SkI p t A bs i0 u' := by
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
    have hws := hT v1 bs[j].toNat (UInt8.toNat_lt _) (by lk [v1])
    rw [ite_word v1 _ _ _ _ hws]
    by_cases hw : p bs[j].toNat = true
    · simp only [bw, hw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j))) := by lk [v1, v]; exact li
      rw [ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1)) _ (by
        rw [eval_add_c v1 sI _ _ li1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li1]
      refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v1, v]; exact lb, by lk [v1, v]; exact ln,
        ⟨BitVec.ofNat 64 bs[j].toNat, by lk [v1, v]⟩, j + 1, hjl, by lk, Or.inl ⟨by lk [v1, v]; exact hg, ?_⟩⟩
      rw [← hsame, skipL_step p bs j hjl, if_pos hw]
    · simp only [bw, hw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
      rw [ConsLoop.assign_local v1 sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v1, v]; exact hg)]
      refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v1, v]; exact lb, by lk [v1, v]; exact ln,
        ⟨BitVec.ofNat 64 bs[j].toNat, by lk [v1, v]⟩, j, hj, by lk [v1, v]; exact li, Or.inr ⟨by lk, ?_⟩⟩
      rw [← hsame, skipL_step p bs j hjl, if_neg hw]
  · simp only [bw, hjl, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [ConsLoop.assign_local v sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v]; exact hg)]
    refine ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v]; exact lb, by lk [v]; exact ln,
      ⟨c, by lk [v]; exact lc⟩, j, hj, by lk [v]; exact li, Or.inr ⟨by lk, ?_⟩⟩
    rw [← hsame, skipL_end p bs j hjl]

theorem skLoop_spec (p : Nat → Bool) (T : ExpHOL 64) (hT : TestOK p T) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ) (hu : SkI p t A bs i0 u) :
    Stop (evaluateHOLFiniteState u (skLoop T)).1 ∨ ((evaluateHOLFiniteState u (skLoop T)).1 = none ∧
      SkI p t A bs i0 (evaluateHOLFiniteState u (skLoop T)).2 ∧
      (evaluateHOLFiniteState u (skLoop T)).2.locals.lookup sI =
        some (.val (.word (BitVec.ofNat 64 (skipL p bs i0))))) := by
  have := while_stop (vv sG) (skBody T) (SkI p t A bs i0)
    (fun u => SkI p t A bs i0 u ∧ u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 (skipL p bs i0)))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, j, _, li, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hj⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := sk_step p T hT t A bs i0 hb u hu hg
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, by rw [li, hj]⟩,
          fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

/-- **`skipWs` refines its list model**: started with the buffer's address, its length and a
position at most the length, the function stops or returns the model's answer, and the memory,
its domain, the globals and the code are as they were. -/
theorem skFun_spec (p : Nat → Bool) (T : ExpHOL 64) (hT : TestOK p T) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hb : BytesAt t A bs) (hi : i0 ≤ bs.length)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i0)))) :
    Stop (evaluateHOLFiniteState t (skFun T)).1 ∨
      ((evaluateHOLFiniteState t (skFun T)).1 =
          some (.returned (.val (.word (BitVec.ofNat 64 (skipL p bs i0))))) ∧
        (evaluateHOLFiniteState t (skFun T)).2.memory = t.memory ∧
        (evaluateHOLFiniteState t (skFun T)).2.memaddrs = t.memaddrs ∧
        (evaluateHOLFiniteState t (skFun T)).2.globals = t.globals ∧
        (evaluateHOLFiniteState t (skFun T)).2.code = t.code) := by
  unfold skFun
  rw [dec_word_eq t sG _ 1 _ (by simp [evalHOLExact])]
  let t1 := setVarHOLFinite sG (.val (.word 1)) t
  rw [dec_word_eq t1 sC _ 0 _ (by simp [evalHOLExact])]
  let t2 := setVarHOLFinite sC (.val (.word 0)) t1
  have h0 : SkI p t A bs i0 t2 := ⟨rfl, rfl, rfl, rfl, rfl, by lk [t2, t1]; exact lb, by lk [t2, t1]; exact ln,
    ⟨0, by lk [t2]⟩, i0, hi, by lk [t2, t1]; exact li, Or.inl ⟨by lk [t2, t1], rfl⟩⟩
  rcases skLoop_spec p T hT t A bs i0 hb t2 h0 with hs | ⟨hn, hI, hres⟩
  · exact Or.inl (seq_stop t2 (skLoop T) _ hs)
  · right
    obtain ⟨m0, d0, c0, g0, -, -⟩ := hI
    generalize hu : evaluateHOLFiniteState t2 (skLoop T) = r at hn hres m0 d0 c0 g0
    obtain ⟨r1, r2⟩ := r
    simp only at hn hres m0 d0 c0 g0
    subst hn
    rw [seq_normal _ hu, evaluateHOLFiniteState_eq_evaluate_def r2 (.return _)]
    simp [eval_vv r2 sI _ hres, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
      emptyLocalsHOLFinite, m0, d0, c0, g0]

end

end ConPanqueque.Scan
