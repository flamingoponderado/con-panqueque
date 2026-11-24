import ConPanqueque.Scan.Str

/-! # Literal choices: `scanBool`, `scanBinderInfo`

`genChoice` compiles a list of literals with their lengths: the first literal found at `j` returns
`j + len`; none falls through to a fallback.  `choiceL` is its list model. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

def choiceL (bs : List UInt8) (j : Nat) : List (List UInt8 × Nat) → Option Nat
  | [] => none
  | (cs, off) :: r => if litsL bs j cs 0 then some off else choiceL bs j r

def genChoice (fb : ProgHOL 64) : List (List UInt8 × Nat) → ProgHOL 64
  | [] => fb
  | (cs, off) :: r => .seq (.assign .local sOk (.const 1))
      (.seq (genLit cs 0) (.ite (vv sOk) (.return (.op .add [vv sJ, .const (BitVec.ofNat 64 off)]))
        (genChoice fb r)))

section
variable {σ : Type}

theorem genChoice_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (j kl : Nat)
    (hb : BytesAt t A bs) (hj : j + 32 < 2 ^ 64) (fb : ProgHOL 64) (Q : BitVec 64 → Prop) :
    ∀ (cands : List (List UInt8 × Nat)) (u : PanSemStateFiniteExact 64 σ),
      (∀ c ∈ cands, c.1.length ≤ 16 ∧ c.2 ≤ 16) → KF t A bs j kl u →
      (∀ off, choiceL bs j cands = some off → Q (BitVec.ofNat 64 (j + off))) →
      (choiceL bs j cands = none → ∀ u', KF t A bs j kl u' → RetP u' fb Q) →
      RetP u (genChoice fb cands) Q := by
  intro cands
  induction cands with
  | nil => intro u _ hu _ hfb; exact hfb rfl u hu
  | cons c r ih =>
    intro u hl hu hok hfb
    obtain ⟨cs, off⟩ := c
    have h1 := hl (cs, off) (List.mem_cons_self ..)
    simp only at h1
    obtain ⟨_, _, _, _, _, _, _, lj, _, _, _, ⟨wo, lo⟩⟩ := id hu
    unfold genChoice
    let u1 := setVarHOLFinite sOk (.val (.word 1)) u
    have hu1 : KF t A bs j kl u1 := kf_set t u A bs j kl hu sOk _ (Or.inr (Or.inr rfl))
    obtain ⟨u2, e2, hu2, lo2, -⟩ := genLit_spec t A bs j kl hb cs 0 true u1 hu1 (by omega) (by lk [u1]; rfl)
    obtain ⟨m1, d1, c1, g1, b1, -⟩ := hu1
    obtain ⟨m2, d2, c2, g2, b2, _, _, lj2, -⟩ := id hu2
    obtain ⟨m0, d0, c0, g0, b0, -⟩ := hu
    refine retP_seq (ConsLoop.assign_local u sOk (.const 1) 1 wo (by simp [evalHOLExact]) lo) ?_ rfl rfl rfl rfl rfl
    refine retP_seq e2 ?_ (m2.trans m1.symm) (d2.trans d1.symm) (g2.trans g1.symm) (c2.trans c1.symm)
      (b2.trans b1.symm)
    refine retP_ite (eval_vv u2 sOk _ lo2) (fun hw => ?_) (fun hw => ?_)
    · have hlit : litsL bs j cs 0 = true := by
        cases h : litsL bs j cs 0
        · simp [bw, h] at hw
        · rfl
      have hq := hok off (by simp [choiceL, hlit])
      right
      have hev := eval_add_c u2 sJ _ (BitVec.ofNat 64 off) lj2
      have hsum : BitVec.ofNat 64 j + BitVec.ofNat 64 off = BitVec.ofNat 64 (j + off) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
      rw [hsum] at hev
      rw [evaluateHOLFiniteState_eq_evaluate_def u2 (.return _)]
      refine ⟨BitVec.ofNat 64 (j + off), ?_, hq, ?_⟩ <;>
        simp [hev, shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite]
    · have hlit : ¬ litsL bs j cs 0 = true := by intro h; simp [bw, h] at hw
      exact ih u2 (fun c hc => hl c (List.mem_cons_of_mem _ hc)) hu2
        (fun o ho => hok o (by simp [choiceL, hlit, ho]))
        (fun hn => hfb (by simp [choiceL, hlit, hn]))

def boolCands : List (List UInt8 × Nat) := [([116, 114, 117, 101], 4), ([102, 97, 108, 115, 101], 5)]

/-- `scanBool(b, n, i)`: the position after `true` or `false` at `i`; anything else is rejected.
The value is the byte at `i` (`t` or `f`). -/
def sbFun : ProgHOL 64 :=
  .dec sJ .one (vv sI) (.dec sL .one (.const 0) (.dec sX .one (.const 0) (.dec sY .one (.const 0)
    (.dec sOk .one (.const 0) (genChoice hang boolCands)))))

/-- The literal-choice functions' entry: `j` at `i`, scratch locals declared. -/
theorem choiceEntry (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i : Nat)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i)))) (body : ProgHOL 64)
    (P : BitVec 64 → Prop)
    (h : ∀ u, KF t A bs i 0 u → RetP u body P) :
    RetP t (.dec sJ .one (vv sI) (.dec sL .one (.const 0) (.dec sX .one (.const 0) (.dec sY .one (.const 0)
      (.dec sOk .one (.const 0) body))))) P := by
  refine retP_dec (eval_vv t sI _ li) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  refine retP_dec (w := 0) (by simp [evalHOLExact]) ?_
  apply h
  exact ⟨rfl, rfl, rfl, rfl, rfl, by lk; exact lb, by lk; exact ln, by lk, by lk; rfl, ⟨0, by lk⟩, ⟨0, by lk⟩, ⟨0, by lk⟩⟩

theorem sbFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i : Nat)
    (hb : BytesAt t A bs) (hi : i + 32 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i)))) :
    RetP t sbFun (fun w => ∃ off, choiceL bs i boolCands = some off ∧ w = BitVec.ofNat 64 (i + off)) :=
  choiceEntry t A bs i lb ln li _ _ (fun u hu =>
    genChoice_spec t A bs i 0 hb hi hang _ boolCands u (by decide) hu (fun off h => ⟨off, h, rfl⟩)
      (fun _ u' _ => retP_hang u' _))

/-- **`scanBool` in Pancake is sound for con-leche's `scanBool`**. -/
theorem sbFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat + 32 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t sbFun (fun w => ∃ (e : USize) (x : Bool), w = BitVec.ofNat 64 e.toNat ∧
      ConLeche.Frontend.scanBool b i = .ok x e) := by
  rcases sbFun_spec t A b.data.toList i.toNat hb hi lb (by simpa using ln) li with hs | ⟨w, r1, ⟨off, hc, rfl⟩, r2⟩
  · exact Or.inl hs
  · right
    refine ⟨_, r1, ?_, r2⟩
    have st : "true".toUTF8.size = 4 := by decide
    have sf : "false".toUTF8.size = 5 := by decide
    have mt := matchLit_L hp "true".toUTF8 (by decide) (by decide) _ i 0 rfl (by rw [st]; simp; omega) (by simp)
    have mf := matchLit_L hp "false".toUTF8 (by decide) (by decide) _ i 0 rfl (by rw [sf]; simp; omega) (by simp)
    have dt : "true".toUTF8.data.toList = [116, 114, 117, 101] := by decide
    have df : "false".toUTF8.data.toList = [102, 97, 108, 115, 101] := by decide
    simp only [dt, df, List.drop_zero, USize.toNat_zero] at mt mf
    have h4 : (i + 4).toNat = i.toNat + 4 := usize_add_toNat hp.bits i 4 (by omega)
    have h5 : (i + 5).toNat = i.toNat + 5 := usize_add_toNat hp.bits i 5 (by omega)
    simp only [choiceL, boolCands] at hc
    rw [ConLeche.Frontend.scanBool, mt, mf]
    split at hc
    · rename_i htrue
      simp only [Option.some.injEq] at hc; subst hc
      exact ⟨i + 4, true, by rw [h4], by simp [htrue]⟩
    · rename_i htrue
      split at hc
      · rename_i hfalse
        simp only [Option.some.injEq] at hc; subst hc
        exact ⟨i + 5, false, by rw [h5], by simp [htrue, hfalse]⟩
      · simp at hc

def binderCands : List (List UInt8 × Nat) := [([34, 100, 101, 102, 97, 117, 108, 116, 34], 9), ([34, 105, 109, 112, 108, 105, 99, 105, 116, 34], 10), ([34, 115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105, 116, 34], 16), ([34, 105, 110, 115, 116, 73, 109, 112, 108, 105, 99, 105, 116, 34], 14)]

/-- `scanBinderInfo(b, n, i)`: the position after a binder-info string at `i`; anything else is
rejected (con-leche's `0`, which every caller rejects). -/
def biFun : ProgHOL 64 :=
  .dec sJ .one (vv sI) (.dec sL .one (.const 0) (.dec sX .one (.const 0) (.dec sY .one (.const 0)
    (.dec sOk .one (.const 0) (genChoice hang binderCands)))))

theorem biFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i : Nat)
    (hb : BytesAt t A bs) (hi : i + 32 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i)))) :
    RetP t biFun (fun w => ∃ off, choiceL bs i binderCands = some off ∧ w = BitVec.ofNat 64 (i + off)) :=
  choiceEntry t A bs i lb ln li _ _ (fun u hu =>
    genChoice_spec t A bs i 0 hb hi hang _ binderCands u (by decide) hu (fun off h => ⟨off, h, rfl⟩)
      (fun _ u' _ => retP_hang u' _))

theorem litsL_quote (bs : List UInt8) (i : Nat) (rest : List UInt8) :
    litsL bs i (34 :: rest) 0 = (byteL bs i == 34 && litsL bs (i + 1) rest 0) := by
  simp only [litsL, Nat.add_zero, litsL_shift]

/-- **`scanBinderInfo` in Pancake is sound for con-leche's**: it returns con-leche's (nonzero)
position. -/
theorem biFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (i : USize) (hi : i.toNat + 32 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t biFun (fun w => ∃ (e : USize), w = BitVec.ofNat 64 e.toNat ∧
      ConLeche.Frontend.scanBinderInfo b i = e ∧ e ≠ 0) := by
  rcases biFun_spec t A b.data.toList i.toNat hb hi lb (by simpa using ln) li with hs | ⟨w, r1, ⟨off, hc, rfl⟩, r2⟩
  · exact Or.inl hs
  · right
    refine ⟨_, r1, ?_, r2⟩
    have hi1 : (i + 1).toNat = i.toNat + 1 := usize_add_toNat hp.bits i 1 (by omega)
    have m1 := matchLit_L hp "default\"".toUTF8 (by decide) (by decide) _ (i + 1) 0 rfl
      (by rw [hi1, show "default\"".toUTF8.size = 8 by decide]; simp; omega) (by simp)
    have m2 := matchLit_L hp "implicit\"".toUTF8 (by decide) (by decide) _ (i + 1) 0 rfl
      (by rw [hi1, show "implicit\"".toUTF8.size = 9 by decide]; simp; omega) (by simp)
    have m3 := matchLit_L hp "strictImplicit\"".toUTF8 (by decide) (by decide) _ (i + 1) 0 rfl
      (by rw [hi1, show "strictImplicit\"".toUTF8.size = 15 by decide]; simp; omega) (by simp)
    have m4 := matchLit_L hp "instImplicit\"".toUTF8 (by decide) (by decide) _ (i + 1) 0 rfl
      (by rw [hi1, show "instImplicit\"".toUTF8.size = 13 by decide]; simp; omega) (by simp)
    simp only [show "default\"".toUTF8.data.toList = [100, 101, 102, 97, 117, 108, 116, 34] by decide,
      show "implicit\"".toUTF8.data.toList = [105, 109, 112, 108, 105, 99, 105, 116, 34] by decide,
      show "strictImplicit\"".toUTF8.data.toList = [115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105, 116, 34] by decide,
      show "instImplicit\"".toUTF8.data.toList = [105, 110, 115, 116, 73, 109, 112, 108, 105, 99, 105, 116, 34] by decide, List.drop_zero, USize.toNat_zero, hi1] at m1 m2 m3 m4
    simp only [choiceL, binderCands, litsL_quote] at hc
    have hq : ∀ x, (ConLeche.Frontend.byteAt b i != 34) = x → (byteL b.data.toList i.toNat == 34) = !x := by
      intro x hx; rw [← hx, byteAt_eq hp]; simp only [byteL, bne, Bool.not_not]
    rw [ConLeche.Frontend.scanBinderInfo, m1, m2, m3, m4]
    have h9 : (i + 9).toNat = i.toNat + 9 := usize_add_toNat hp.bits i 9 (by omega)
    have h10 : (i + 10).toNat = i.toNat + 10 := usize_add_toNat hp.bits i 10 (by omega)
    have h16 : (i + 16).toNat = i.toNat + 16 := usize_add_toNat hp.bits i 16 (by omega)
    have h14 : (i + 14).toNat = i.toNat + 14 := usize_add_toNat hp.bits i 14 (by omega)
    generalize hbq : (ConLeche.Frontend.byteAt b i != 34) = x
    have hq' := hq x hbq
    rw [hq'] at hc
    cases x <;> simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at hc ⊢
    · split at hc
      · rename_i h; simp only [Option.some.injEq] at hc; subst hc
        refine ⟨i + 9, by rw [h9], by simp [h], ?_⟩
        intro e; have := congrArg USize.toNat e; rw [h9] at this; simp at this
      split at hc
      · rename_i h1 h; simp only [Option.some.injEq] at hc; subst hc
        refine ⟨i + 10, by rw [h10], by simp [h1, h], ?_⟩
        intro e; have := congrArg USize.toNat e; rw [h10] at this; simp at this
      split at hc
      · rename_i h1 h2 h; simp only [Option.some.injEq] at hc; subst hc
        refine ⟨i + 16, by rw [h16], by simp [h1, h2, h], ?_⟩
        intro e; have := congrArg USize.toNat e; rw [h16] at this; simp at this
      split at hc
      · rename_i h1 h2 h3 h; simp only [Option.some.injEq] at hc; subst hc
        refine ⟨i + 14, by rw [h14], by simp [h1, h2, h3, h], ?_⟩
        intro e; have := congrArg USize.toNat e; rw [h14] at this; simp at this
      simp at hc
    · simp at hc

end

end ConPanqueque.Scan
