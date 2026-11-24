import ConPanqueque.Scan.Keys
import ConPanqueque.Scan.NumEnd
import ConPanqueque.Scan.ReadNat

/-! # The key classifier in Pancake, compiled from `keyTbl`

`genBytes`/`genLens`/`genFirst`/`genLit` compile a key table to nested Pancake conditionals; one
proof by induction over the table says the code returns the table's interpreter's answer
(`evalKL`), and `keyAt_L` makes that con-leche's `keyAt`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def sL := ofString "kl"
def sX := ofString "x"
def sY := ofString "y"
def sOk := ofString "ok"
def sJ := ofString "j"

/-- `dst = byteAt(pos)`: the byte, or `0` past the end. -/
def bAt (dst : MlS) (pos : ExpHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower pos (vv sN)) (.assign .local dst (.loadByte (.op .add [vv sB, pos])))
    (.assign .local dst (.const 0))

def posE (k : Nat) : ExpHOL 64 := .op .add [vv sJ, .const (BitVec.ofNat 64 k)]

def genLit : List UInt8 → Nat → ProgHOL 64
  | [], _ => .skip
  | c :: cs, k => .seq (bAt sY (posE k))
      (.seq (.assign .local sOk (.op .and [vv sOk, .cmp .equal (vv sY) (.const (BitVec.ofNat 64 c.toNat))]))
        (genLit cs (k + 1)))

def retK (k : ConLeche.Frontend.Key) : ProgHOL 64 := .return (.const (BitVec.ofNat 64 k.ctorIdx))

def genFirst : List (List UInt8 × ConLeche.Frontend.Key) → ProgHOL 64
  | [] => retK .kUnknown
  | (cs, k) :: r => .seq (.assign .local sOk (.const 1))
      (.seq (genLit cs 0) (.ite (vv sOk) (retK k) (genFirst r)))

def genLens : List (USize × List (List UInt8 × ConLeche.Frontend.Key)) → ProgHOL 64
  | [] => retK .kUnknown
  | (l, cs) :: r => .ite (.cmp .equal (vv sL) (.const (BitVec.ofNat 64 l.toNat))) (genFirst cs) (genLens r)

def genBytes : KeyTbl → ProgHOL 64
  | [] => retK .kUnknown
  | (y, lens) :: r => .ite (.cmp .equal (vv sX) (.const (BitVec.ofNat 64 y.toNat))) (genLens lens) (genBytes r)

/-- `keyAt(b, n, i, kl)`. -/
def kaFun : ProgHOL 64 :=
  .dec sX .one (.const 0) (.dec sY .one (.const 0) (.dec sOk .one (.const 0)
    (.dec sJ .one (.op .add [vv sI, .const 2])
      (.seq (bAt sX (.op .add [vv sI, .const 1])) (genBytes keyTbl)))))

section
variable {σ : Type}

theorem bw_eq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) then
      (1 : BitVec 64) else 0) = bw (x = y) := by
  by_cases h : x = y
  · simp [h, bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : ¬ BitVec.ofNat 64 x = BitVec.ofNat 64 y := fun e => h ((ofNat_inj x y hx hy).mp e)
    simp [h, bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]

theorem bAt_spec (u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (dst : MlS)
    (pos : ExpHOL 64) (p : Nat) (hb : BytesAt u A bs) (hp : p < 2 ^ 64) (w0 : BitVec 64)
    (hd : u.locals.lookup dst = some (.val (.word w0)))
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (hpos : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) pos =
      some (.val (.word (BitVec.ofNat 64 p)))) :
    evaluateHOLFiniteState u (bAt dst pos) =
      (none, setVarHOLFinite dst (.val (.word (BitVec.ofNat 64 (byteL bs p).toNat))) u) := by
  have hL : bs.length < 2 ^ 64 := by have := hb.2.2.1; omega
  unfold bAt
  rw [ite_word u _ _ _ _ (ConsLoop.eval_cmp_of u .lower _ _ _ _ hpos (eval_vv u sN _ ln))]
  by_cases hlt : p < bs.length
  · have : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 p) (BitVec.ofNat 64 bs.length) = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_lt_iff p bs.length hp hL, hlt]
    simp only [this, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have haddr : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (.op .add [vv sB, pos]) = some (.val (.word (A + BitVec.ofNat 64 p))) := by
      simp [vv, evalHOLExact, evalListHOLExact, lb, hpos, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [ConsLoop.assign_local u dst _ _ w0 (eval_loadByte_bytes u _ A bs p hb hlt haddr) hd]
    simp [byteL, List.getElem?_eq_getElem hlt]
  · have : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 p) (BitVec.ofNat 64 bs.length) = false := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_lt_iff p bs.length hp hL, hlt]
    simp only [this, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [ConsLoop.assign_local u dst _ 0 w0 (by simp [evalHOLExact]) hd]
    have : byteL bs p = 0 := by simp [byteL, List.getElem?_eq_none (by omega : bs.length ≤ p)]
    rw [this]; rfl

/-- The classifier's frame: the buffer, `j`, the key length, and scratch words. -/
def KF (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) ∧
  u.locals.lookup sJ = some (.val (.word (BitVec.ofNat 64 j))) ∧
  u.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 kl))) ∧
  (∃ w, u.locals.lookup sX = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sY = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sOk = some (.val (.word w)))

theorem kf_set (t u : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (h : KF t A bs j kl u) (x : MlS) (w : BitVec 64) (hx : x = sX ∨ x = sY ∨ x = sOk) :
    KF t A bs j kl (setVarHOLFinite x (.val (.word w)) u) := by
  obtain ⟨m, d, c, g, b, lb, ln, lj, ll, ⟨wx, lx⟩, ⟨wy, ly⟩, ⟨wo, lo⟩⟩ := h
  rcases hx with rfl | rfl | rfl
  · exact ⟨m, d, c, g, b, by lk; exact lb, by lk; exact ln, by lk; exact lj, by lk; exact ll,
      ⟨w, by lk⟩, ⟨wy, by lk; exact ly⟩, ⟨wo, by lk; exact lo⟩⟩
  · exact ⟨m, d, c, g, b, by lk; exact lb, by lk; exact ln, by lk; exact lj, by lk; exact ll,
      ⟨wx, by lk; exact lx⟩, ⟨w, by lk⟩, ⟨wo, by lk; exact lo⟩⟩
  · exact ⟨m, d, c, g, b, by lk; exact lb, by lk; exact ln, by lk; exact lj, by lk; exact ll,
      ⟨wx, by lk; exact lx⟩, ⟨wy, by lk; exact ly⟩, ⟨w, by lk⟩⟩

theorem genLit_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (hb : BytesAt t A bs) :
    ∀ (cs : List UInt8) (k : Nat) (ok : Bool) (u : PanSemStateFiniteExact 64 σ), KF t A bs j kl u →
      j + k + cs.length < 2 ^ 64 →
      u.locals.lookup sOk = some (.val (.word (bw (ok = true)))) →
      ∃ u', evaluateHOLFiniteState u (genLit cs k) = (none, u') ∧ KF t A bs j kl u' ∧
        u'.locals.lookup sOk = some (.val (.word (bw ((ok && litsL bs j cs k) = true)))) ∧
        u'.locals.lookup sX = u.locals.lookup sX := by
  intro cs
  induction cs with
  | nil =>
    intro k ok u hu _ lo
    refine ⟨u, by rw [genLit, skip_eval], hu, by simp [litsL]; exact lo, rfl⟩
  | cons c cs ih =>
    intro k ok u hu hk lo
    obtain ⟨m, d, cc, g, bb, lb, ln, lj, ll, _, ⟨wy, ly⟩, _⟩ := id hu
    have hbu : BytesAt u A bs := bytesAt_congr hb m d bb
    have hpos : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
        (posE k) = some (.val (.word (BitVec.ofNat 64 (j + k)))) := by
      unfold posE; rw [eval_add_c u sJ _ _ lj]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega
    rw [genLit, seq_normal _ (bAt_spec u A bs sY _ (j + k) hbu (by simp at hk; omega) wy ly lb ln hpos)]
    let u1 := setVarHOLFinite sY (.val (.word (BitVec.ofNat 64 (byteL bs (j + k)).toNat))) u
    have lo1 : u1.locals.lookup sOk = some (.val (.word (bw (ok = true)))) := by lk [u1]; exact lo
    have ly1 : u1.locals.lookup sY = some (.val (.word (BitVec.ofNat 64 (byteL bs (j + k)).toNat))) := by lk [u1]
    have hand : @evalHOLExact 64 σ _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
        (.op .and [vv sOk, .cmp .equal (vv sY) (.const (BitVec.ofNat 64 c.toNat))]) =
        some (.val (.word (bw ((ok && (byteL bs (j + k) == c)) = true)))) := by
      have h1 := ConsLoop.eval_cmp_of u1 .equal (vv sY) (.const (BitVec.ofNat 64 c.toNat)) _ (BitVec.ofNat 64 c.toNat)
        (eval_vv u1 sY _ ly1) (by simp [evalHOLExact])
      rw [bw_eq _ _ (by have := UInt8.toNat_lt (byteL bs (j + k)); omega)
        (by have := UInt8.toNat_lt c; omega)] at h1
      rw [evalHOLExact]
      simp only [evalListHOLExact, eval_vv u1 sOk _ lo1, h1]
      have e : (byteL bs (j + k) == c) = decide ((byteL bs (j + k)).toNat = c.toNat) := by
        by_cases h : byteL bs (j + k) = c
        · simp [h]
        · have : ¬ (byteL bs (j + k)).toNat = c.toNat := fun h' => h (UInt8.toNat_inj.mp h')
          simp [h, this]
      rw [e]
      cases ok <;> by_cases h : (byteL bs (j + k)).toNat = c.toNat <;>
        simp [h, bw, wordOpHOL, wordOp, valueIsWord, valueWord] <;> decide
    rw [seq_normal _ (ConsLoop.assign_local u1 sOk _ _ _ hand lo1)]
    let u2 := setVarHOLFinite sOk (.val (.word (bw ((ok && (byteL bs (j + k) == c)) = true)))) u1
    have hu2 : KF t A bs j kl u2 := kf_set t u1 A bs j kl (kf_set t u A bs j kl hu sY _ (Or.inr (Or.inl rfl)))
      sOk _ (Or.inr (Or.inr rfl))
    obtain ⟨u', e', hu', lo', lx'⟩ := ih (k + 1) (ok && (byteL bs (j + k) == c)) u2 hu2 (by simp at hk; omega) (by lk [u2])
    refine ⟨u', e', hu', ?_, by rw [lx']; lk [u2, u1]⟩
    rw [lo']; simp only [litsL, Bool.and_assoc]; rfl


theorem retSpec_seq {u u1 : PanSemStateFiniteExact 64 σ} {p q : ProgHOL 64} {v : BitVec 64}
    (h : evaluateHOLFiniteState u p = (none, u1)) (hq : RetSpec u1 q v)
    (m : u1.memory = u.memory) (d : u1.memaddrs = u.memaddrs) (g : u1.globals = u.globals)
    (c : u1.code = u.code) (b : u1.be = u.be) : RetSpec u (.seq p q) v := by
  unfold RetSpec at hq ⊢
  rw [seq_normal _ h]
  rcases hq with hs | ⟨r1, r2, r3, r4, r5, r6⟩
  · exact Or.inl hs
  · exact Or.inr ⟨r1, r2.trans m, r3.trans d, r4.trans g, r5.trans c, r6.trans b⟩

theorem retSpec_ite {u : PanSemStateFiniteExact 64 σ} {e : ExpHOL 64} {p q : ProgHOL 64} {v w : BitVec 64}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (hp : w ≠ 0 → RetSpec u p v) (hq : w = 0 → RetSpec u q v) : RetSpec u (.ite e p q) v := by
  unfold RetSpec at hp hq ⊢
  rw [ite_word u _ _ _ _ he]
  by_cases hw : w = 0
  · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte]; exact hq hw
  · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte]; exact hp hw

theorem retK_spec (u : PanSemStateFiniteExact 64 σ) (k : ConLeche.Frontend.Key) :
    RetSpec u (retK k) (BitVec.ofNat 64 k.ctorIdx) := by
  right
  unfold retK
  rw [evaluateHOLFiniteState_eq_evaluate_def u (.return _)]
  simp [evalHOLExact, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,
    emptyLocalsHOLFinite]

theorem retSpec_frame {t u : PanSemStateFiniteExact 64 σ} {c : ProgHOL 64} {v : BitVec 64}
    (h : RetSpec u c v) (m : u.memory = t.memory) (d : u.memaddrs = t.memaddrs) (g : u.globals = t.globals)
    (cc : u.code = t.code) (b : u.be = t.be) : RetSpec u c v := h

theorem genFirst_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (hb : BytesAt t A bs) (hj : j + 16 < 2 ^ 64) :
    ∀ (cands : List (List UInt8 × ConLeche.Frontend.Key)) (u : PanSemStateFiniteExact 64 σ),
      (∀ c ∈ cands, c.1.length ≤ 16) → KF t A bs j kl u →
      RetSpec u (genFirst cands) (BitVec.ofNat 64 (firstL bs j cands).ctorIdx) := by
  intro cands
  induction cands with
  | nil => intro u _ _; exact retK_spec u _
  | cons c r ih =>
    intro u hl hu
    obtain ⟨cs, k⟩ := c
    have h1 := hl (cs, k) (List.mem_cons_self ..)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨wo, lo⟩⟩ := id hu
    unfold genFirst
    let u1 := setVarHOLFinite sOk (.val (.word 1)) u
    have hu1 : KF t A bs j kl u1 := kf_set t u A bs j kl hu sOk _ (Or.inr (Or.inr rfl))
    obtain ⟨u2, e2, hu2, lo2, -⟩ := genLit_spec t A bs j kl hb cs 0 true u1 hu1 (by simp at h1; omega)
      (by lk [u1]; rfl)
    obtain ⟨m1, d1, c1, g1, b1, -⟩ := hu1
    obtain ⟨m2, d2, c2, g2, b2, -⟩ := id hu2
    obtain ⟨m0, d0, c0, g0, b0, -⟩ := hu
    refine retSpec_seq (ConsLoop.assign_local u sOk (.const 1) 1 wo (by simp [evalHOLExact]) lo) ?_ rfl rfl rfl rfl rfl
    refine retSpec_seq e2 ?_ (m2.trans m1.symm) (d2.trans d1.symm) (g2.trans g1.symm) (c2.trans c1.symm)
      (b2.trans b1.symm)
    refine retSpec_ite (eval_vv u2 sOk _ lo2) (fun hw => ?_) (fun hw => ?_)
    · have hlit : litsL bs j cs 0 = true := by
        cases h : litsL bs j cs 0
        · simp [bw, h] at hw
        · rfl
      simp only [firstL, hlit, ↓reduceIte]; exact retK_spec u2 k
    · have hlit : ¬ litsL bs j cs 0 = true := by
        intro h; simp [bw, h] at hw
      simp only [firstL, hlit, Bool.false_eq_true, ↓reduceIte]
      exact ih u2 (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hu2

theorem genLens_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (hb : BytesAt t A bs) (hj : j + 16 < 2 ^ 64) (hkl : kl < 2 ^ 64) :
    ∀ (lens : List (USize × List (List UInt8 × ConLeche.Frontend.Key))) (u : PanSemStateFiniteExact 64 σ),
      (∀ l ∈ lens, ∀ c ∈ l.2, c.1.length ≤ 16) → KF t A bs j kl u →
      RetSpec u (genLens lens) (BitVec.ofNat 64 (lensL bs j kl lens).ctorIdx) := by
  intro lens
  induction lens with
  | nil => intro u _ _; exact retK_spec u _
  | cons l r ih =>
    intro u hl hu
    obtain ⟨len, cs⟩ := l
    obtain ⟨_, _, _, _, _, _, _, _, ll, _⟩ := id hu
    unfold genLens
    have hc := ConsLoop.eval_cmp_of u .equal (vv sL) (.const (BitVec.ofNat 64 len.toNat)) _
      (BitVec.ofNat 64 len.toNat) (eval_vv u sL _ ll) (by simp [evalHOLExact])
    rw [bw_eq _ _ hkl (Nat.lt_of_lt_of_le (USize.toNat_lt_two_pow_numBits len)
      (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega)))] at hc
    refine retSpec_ite hc (fun hw => ?_) (fun hw => ?_)
    · have h : kl = len.toNat := by
        cases hh : decide (kl = len.toNat) <;> simp_all [bw]
      simp only [lensL, h, ↓reduceIte]
      exact genFirst_spec t A bs j kl hb hj cs u (hl _ (List.mem_cons_self ..)) hu
    · have h : ¬ kl = len.toNat := by intro h; simp [bw, h] at hw
      simp only [lensL, h, ↓reduceIte]
      exact ih u (fun l hl' => hl l (List.mem_cons_of_mem _ hl')) hu

theorem genBytes_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (x : UInt8) (hb : BytesAt t A bs) (hj : j + 16 < 2 ^ 64) (hkl : kl < 2 ^ 64) :
    ∀ (tb : KeyTbl) (u : PanSemStateFiniteExact 64 σ),
      (∀ e ∈ tb, ∀ l ∈ e.2, ∀ c ∈ l.2, c.1.length ≤ 16) → KF t A bs j kl u →
      u.locals.lookup sX = some (.val (.word (BitVec.ofNat 64 x.toNat))) →
      RetSpec u (genBytes tb) (BitVec.ofNat 64 (bytesL bs j kl x tb).ctorIdx) := by
  intro tb
  induction tb with
  | nil => intro u _ _ _; exact retK_spec u _
  | cons e r ih =>
    intro u hl hu lx
    obtain ⟨y, lens⟩ := e
    unfold genBytes
    have hc := ConsLoop.eval_cmp_of u .equal (vv sX) (.const (BitVec.ofNat 64 y.toNat)) _
      (BitVec.ofNat 64 y.toNat) (eval_vv u sX _ lx) (by simp [evalHOLExact])
    rw [bw_eq _ _ (by have := UInt8.toNat_lt x; omega) (by have := UInt8.toNat_lt y; omega)] at hc
    refine retSpec_ite hc (fun hw => ?_) (fun hw => ?_)
    · have h : x = y := by
        apply UInt8.toNat_inj.mp
        cases hh : decide (x.toNat = y.toNat) <;> simp_all [bw]
      simp only [bytesL, h, ↓reduceIte]
      exact genLens_spec t A bs j kl hb hj hkl lens u (hl _ (List.mem_cons_self ..)) hu
    · have h : ¬ x = y := by intro h; simp [bw, h] at hw
      simp only [bytesL, h, ↓reduceIte]
      exact ih u (fun e he => hl e (List.mem_cons_of_mem _ he)) hu lx

theorem retSpec_dec {u : PanSemStateFiniteExact 64 σ} {x : MlS} {e : ExpHOL 64} {body : ProgHOL 64}
    {w v : BitVec 64}
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e =
      some (.val (.word w)))
    (h : RetSpec (setVarHOLFinite x (.val (.word w)) u) body v) : RetSpec u (.dec x .one e body) v := by
  unfold RetSpec at h ⊢
  rw [dec_word_eq u x e w body he]
  exact h

theorem kaFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i kl : Nat)
    (hb : BytesAt t A bs) (hi : i + 18 < 2 ^ 64) (hkl : kl < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 kl)))) :
    RetSpec t kaFun (BitVec.ofNat 64 (evalKL bs i kl).ctorIdx) := by
  unfold kaFun
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retSpec_dec (w := 0) (by simp [evalHOLExact]) ?_
  let t3 := setVarHOLFinite sOk (.val (.word 0)) (setVarHOLFinite sY (.val (.word 0))
    (setVarHOLFinite sX (.val (.word 0)) t))
  have li3 : t3.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i))) := by lk [t3]; exact li
  refine retSpec_dec (w := BitVec.ofNat 64 (i + 2)) (by
    rw [eval_add_c t3 sI _ _ li3]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega) ?_
  let t4 := setVarHOLFinite sJ (.val (.word (BitVec.ofNat 64 (i + 2)))) t3
  have hb4 : BytesAt t4 A bs := bytesAt_congr hb rfl rfl rfl
  have hpos : @evalHOLExact 64 σ _ t4.toExact (fun a => Classical.propDecidable (t4.memaddrs a))
      (.op .add [vv sI, .const 1]) = some (.val (.word (BitVec.ofNat 64 (i + 1)))) := by
    rw [eval_add_c t4 sI _ _ (by lk [t4]; exact li3)]; congr 3; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]; try omega
  have e := bAt_spec t4 A bs sX _ (i + 1) hb4 (by omega) 0 (by lk [t4, t3]) (by lk [t4, t3]; exact lb)
    (by lk [t4, t3]; exact ln) hpos
  let t5 := setVarHOLFinite sX (.val (.word (BitVec.ofNat 64 (byteL bs (i + 1)).toNat))) t4
  have hkf : KF t A bs (i + 2) kl t5 := ⟨rfl, rfl, rfl, rfl, rfl, by lk [t5, t4, t3]; exact lb,
    by lk [t5, t4, t3]; exact ln, by lk [t5, t4], by lk [t5, t4, t3]; exact ll,
    ⟨BitVec.ofNat 64 (byteL bs (i + 1)).toNat, by lk [t5]⟩,
    ⟨0, by lk [t5, t4, t3]⟩, ⟨0, by lk [t5, t4, t3]⟩⟩
  refine retSpec_seq e ?_ rfl rfl rfl rfl rfl
  exact genBytes_spec t A bs (i + 2) kl _ hb (by omega) hkl keyTbl t5 keyTbl_short hkf (by lk [t5])

/-- **`keyAt` in Pancake is con-leche's `keyAt`**: the key's index (`Key.ctorIdx`). -/
theorem keyAt_refines (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i kl : USize) (hi : i.toNat + 18 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 kl.toNat)))) :
    RetSpec t kaFun (BitVec.ofNat 64 (ConLeche.Frontend.keyAt b i kl).ctorIdx) := by
  rw [keyAt_L hp i kl hi]
  have hkl : kl.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (USize.toNat_lt_two_pow_numBits kl)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega))
  exact kaFun_spec t A b.data.toList i.toNat kl.toNat hb hi hkl lb (by simpa using ln) li ll

end

end ConPanqueque.Scan
