import ConPanqueque.T.Core.AndRescue
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Handle-list equality in the environment heap

Two environment blocks of handles are equal lists iff their lengths and all their words agree (a recursive
function over the index from the given position). Handle equality is word equality (`idxW` is injective).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def lqA := ofString "lqa"
def lqB := ofString "lqb"
def lqI := ofString "lqi"
def lqN := ofString "lqn"
def lqX := ofString "lqx"
def lqY := ofString "lqy"
def lqR := ofString "lqr"
def fLq := ofString "envListEqFrom"

@[simp] theorem lq_lqA_ne_lqB : lqA ≠ lqB := by decide
@[simp] theorem lq_lqA_ne_lqI : lqA ≠ lqI := by decide
@[simp] theorem lq_lqA_ne_lqN : lqA ≠ lqN := by decide
@[simp] theorem lq_lqA_ne_lqX : lqA ≠ lqX := by decide
@[simp] theorem lq_lqA_ne_lqY : lqA ≠ lqY := by decide
@[simp] theorem lq_lqA_ne_lqR : lqA ≠ lqR := by decide
@[simp] theorem lq_lqA_ne_lKb : lqA ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqA : lKb ≠ lqA := by decide
@[simp] theorem lq_lqB_ne_lqA : lqB ≠ lqA := by decide
@[simp] theorem lq_lqB_ne_lqI : lqB ≠ lqI := by decide
@[simp] theorem lq_lqB_ne_lqN : lqB ≠ lqN := by decide
@[simp] theorem lq_lqB_ne_lqX : lqB ≠ lqX := by decide
@[simp] theorem lq_lqB_ne_lqY : lqB ≠ lqY := by decide
@[simp] theorem lq_lqB_ne_lqR : lqB ≠ lqR := by decide
@[simp] theorem lq_lqB_ne_lKb : lqB ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqB : lKb ≠ lqB := by decide
@[simp] theorem lq_lqI_ne_lqA : lqI ≠ lqA := by decide
@[simp] theorem lq_lqI_ne_lqB : lqI ≠ lqB := by decide
@[simp] theorem lq_lqI_ne_lqN : lqI ≠ lqN := by decide
@[simp] theorem lq_lqI_ne_lqX : lqI ≠ lqX := by decide
@[simp] theorem lq_lqI_ne_lqY : lqI ≠ lqY := by decide
@[simp] theorem lq_lqI_ne_lqR : lqI ≠ lqR := by decide
@[simp] theorem lq_lqI_ne_lKb : lqI ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqI : lKb ≠ lqI := by decide
@[simp] theorem lq_lqN_ne_lqA : lqN ≠ lqA := by decide
@[simp] theorem lq_lqN_ne_lqB : lqN ≠ lqB := by decide
@[simp] theorem lq_lqN_ne_lqI : lqN ≠ lqI := by decide
@[simp] theorem lq_lqN_ne_lqX : lqN ≠ lqX := by decide
@[simp] theorem lq_lqN_ne_lqY : lqN ≠ lqY := by decide
@[simp] theorem lq_lqN_ne_lqR : lqN ≠ lqR := by decide
@[simp] theorem lq_lqN_ne_lKb : lqN ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqN : lKb ≠ lqN := by decide
@[simp] theorem lq_lqX_ne_lqA : lqX ≠ lqA := by decide
@[simp] theorem lq_lqX_ne_lqB : lqX ≠ lqB := by decide
@[simp] theorem lq_lqX_ne_lqI : lqX ≠ lqI := by decide
@[simp] theorem lq_lqX_ne_lqN : lqX ≠ lqN := by decide
@[simp] theorem lq_lqX_ne_lqY : lqX ≠ lqY := by decide
@[simp] theorem lq_lqX_ne_lqR : lqX ≠ lqR := by decide
@[simp] theorem lq_lqX_ne_lKb : lqX ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqX : lKb ≠ lqX := by decide
@[simp] theorem lq_lqY_ne_lqA : lqY ≠ lqA := by decide
@[simp] theorem lq_lqY_ne_lqB : lqY ≠ lqB := by decide
@[simp] theorem lq_lqY_ne_lqI : lqY ≠ lqI := by decide
@[simp] theorem lq_lqY_ne_lqN : lqY ≠ lqN := by decide
@[simp] theorem lq_lqY_ne_lqX : lqY ≠ lqX := by decide
@[simp] theorem lq_lqY_ne_lqR : lqY ≠ lqR := by decide
@[simp] theorem lq_lqY_ne_lKb : lqY ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqY : lKb ≠ lqY := by decide
@[simp] theorem lq_lqR_ne_lqA : lqR ≠ lqA := by decide
@[simp] theorem lq_lqR_ne_lqB : lqR ≠ lqB := by decide
@[simp] theorem lq_lqR_ne_lqI : lqR ≠ lqI := by decide
@[simp] theorem lq_lqR_ne_lqN : lqR ≠ lqN := by decide
@[simp] theorem lq_lqR_ne_lqX : lqR ≠ lqX := by decide
@[simp] theorem lq_lqR_ne_lqY : lqR ≠ lqY := by decide
@[simp] theorem lq_lqR_ne_lKb : lqR ≠ lKb := by decide
@[simp] theorem lq_lKb_ne_lqR : lKb ≠ lqR := by decide

def lqParams : List MlS := [lqA, lqB, lqI, lqN]
def lqLocals : List MlS := [lqX, lqY, lqR]

/-- `lqA`, `lqB`: the blocks' first element cells; compare positions `i..n`. -/
def lqBody : ProgHOL 64 := prologue lqLocals
  (.ite (.cmp .equal (vv lqI) (vv lqN)) (.return (.const 1))
  (.seq (.assign .local lqX (.load .one (.op .add [vv lqA, .shift .lsl (vv lqI) (.const 3)])))
  (.seq (.assign .local lqY (.load .one (.op .add [vv lqB, .shift .lsl (vv lqI) (.const 3)])))
  (.ite (.cmp .notEqual (vv lqX) (vv lqY)) (.return (.const 0))
  (.seq (.call (some (some (.local, lqR), none)) fLq [vv lqA, vv lqB, .op .add [vv lqI, .const 1], vv lqN])
    (.return (vv lqR)))))))

section
variable {σ : Type}

theorem lq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lqLocals → (ctxEnv C ++ lqParams.zip vals).get x = none :=
  Knot.params_none C lqLocals lqParams vals (by decide) (by decide)

theorem ecell_shl3 (C : Ctx) (o i : Nat) (hi : i < 2 ^ 60) :
    ecell C o + BitVec.ofNat 64 i <<< (3 : Nat) = ecell C (o + i) := by
  rw [Str.w_shl _ _ (by omega), show i * 2 ^ 3 = 8 * i by omega, ecell_add]

/-- The list comparison from position `i`, as a pure answer. -/
theorem lq_spec (C : Ctx) (hcf : C.code.lookup fLq = some (lqParams.map (fun p => (p, ShapeHOL.one)), lqBody, .one))
    (xs ys : List NIdx) (oa ob : Nat) (hn : xs.length = ys.length) (hlen : xs.length < 2 ^ 60)
    (ha : ∀ i (hi : i < xs.length), C.EH[oa + i]? = some (Enc.idxW xs[i]))
    (hb : ∀ i (hi : i < ys.length), C.EH[ob + i]? = some (Enc.idxW ys[i])) (s : AState) :
    ∀ k i, xs.length - i = k → i ≤ xs.length →
      SpecR (σ := σ) (Pre C s (lqParams.zip [ecell C oa, ecell C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        lqBody s (pure (xs.drop i == ys.drop i) : AM Bool) (Knot.PostB C) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have hi' : i = xs.length := by omega
    subst hi'
    refine specR_prologue (Knot.postB_locals C) (lq_none C _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW true) rfl
      (fun t ht => ⟨C.H, List.prefix_refl _, by simp [hn, boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i hk hi
    have hil : i < xs.length := by omega
    refine specR_prologue (Knot.postB_locals C) (lq_none C _) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 xs.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI lqX _ (oa + i) _ (by decide)
      (by simp +decide [sev, Env.get, lqParams, ctxEnv]; exact ecell_shl3 C oa i (by omega)) (ha i hil) ?_
    refine specR_envLoadI lqY _ (ob + i) _ (by decide)
      (by simp +decide [sev, Env.get, lqParams, ctxEnv]; exact ecell_shl3 C ob i (by omega)) (hb i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hil, List.drop_eq_getElem_cons (show i < ys.length by omega)]
    by_cases he : xs[i] = ys[i]'(by omega)
    · have hw : Enc.idxW xs[i] = Enc.idxW (ys[i]'(by omega)) := by rw [he]
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h)
        (fun _ => ?_)
      have hrw : (xs[i] :: xs.drop (i + 1) == (ys[i]'(by omega)) :: ys.drop (i + 1)) = (xs.drop (i + 1) == ys.drop (i + 1)) := by
        rw [List.cons_beq_cons, he, beq_self_eq_true, Bool.true_and]
      rw [hrw]
      refine specR_congr (m' := (pure (xs.drop (i + 1) == ys.drop (i + 1)) : AM Bool) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH lqR fLq lqParams [vv lqA, vv lqB, .op .add [vv lqI, .const 1], vv lqN] lqBody
        [ecell C oa, ecell C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hcf
        ⟨by simp +decide [Env.get, lqParams, ctxEnv], by simp +decide [Env.get, lqParams, ctxEnv],
          by simp +decide [sev, Env.get, lqParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, lqParams, ctxEnv],
          trivial⟩
        (Knot.PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lqParams _ rfl hlk) (ih (i + 1) (by omega) (by omega)))
        (fun b w s' H' hp hw => ?_)
      subst hw
      exact specR_returnI _ (boolW b) (by simp) (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hw : Enc.idxW xs[i] ≠ Enc.idxW (ys[i]'(by omega)) := fun e => he (Enc.idxW_inj e)
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _,
          by rw [List.cons_beq_cons, beq_eq_false_iff_ne.mpr he, Bool.false_and], sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
