import ConPanqueque.T.Core.IotaFamBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Memo lists in the value heap

The twin's per-call walks (`wscopedBGo`, `leavesSubGo`, `fvarLeavesGo`) thread a functional memo through their
results. The port keeps it as a heap list of nodes `[k₁, k₂, v, next]`, newest first (`0` is empty): an insert
allocates a node, so the heap only grows; a lookup returns the first match (`mlLk`), which is the latest insert,
as `HashMap.insert` overwrites.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def mlP := ofString "mlp"
def mlA := ofString "mla"
def mlB := ofString "mlb"
def mlX := ofString "mlx"
def mlY := ofString "mly"
def mlR := ofString "mlr"
def fMl := ofString "memoLookup"

@[simp] theorem ml_mlP_ne_mlA : mlP ≠ mlA := by decide
@[simp] theorem ml_mlP_ne_mlB : mlP ≠ mlB := by decide
@[simp] theorem ml_mlP_ne_mlX : mlP ≠ mlX := by decide
@[simp] theorem ml_mlP_ne_mlY : mlP ≠ mlY := by decide
@[simp] theorem ml_mlP_ne_mlR : mlP ≠ mlR := by decide
@[simp] theorem ml_mlP_ne_lKb : mlP ≠ lKb := by decide
@[simp] theorem ml_mlA_ne_mlP : mlA ≠ mlP := by decide
@[simp] theorem ml_mlA_ne_mlB : mlA ≠ mlB := by decide
@[simp] theorem ml_mlA_ne_mlX : mlA ≠ mlX := by decide
@[simp] theorem ml_mlA_ne_mlY : mlA ≠ mlY := by decide
@[simp] theorem ml_mlA_ne_mlR : mlA ≠ mlR := by decide
@[simp] theorem ml_mlA_ne_lKb : mlA ≠ lKb := by decide
@[simp] theorem ml_mlB_ne_mlP : mlB ≠ mlP := by decide
@[simp] theorem ml_mlB_ne_mlA : mlB ≠ mlA := by decide
@[simp] theorem ml_mlB_ne_mlX : mlB ≠ mlX := by decide
@[simp] theorem ml_mlB_ne_mlY : mlB ≠ mlY := by decide
@[simp] theorem ml_mlB_ne_mlR : mlB ≠ mlR := by decide
@[simp] theorem ml_mlB_ne_lKb : mlB ≠ lKb := by decide
@[simp] theorem ml_mlX_ne_mlP : mlX ≠ mlP := by decide
@[simp] theorem ml_mlX_ne_mlA : mlX ≠ mlA := by decide
@[simp] theorem ml_mlX_ne_mlB : mlX ≠ mlB := by decide
@[simp] theorem ml_mlX_ne_mlY : mlX ≠ mlY := by decide
@[simp] theorem ml_mlX_ne_mlR : mlX ≠ mlR := by decide
@[simp] theorem ml_mlX_ne_lKb : mlX ≠ lKb := by decide
@[simp] theorem ml_mlY_ne_mlP : mlY ≠ mlP := by decide
@[simp] theorem ml_mlY_ne_mlA : mlY ≠ mlA := by decide
@[simp] theorem ml_mlY_ne_mlB : mlY ≠ mlB := by decide
@[simp] theorem ml_mlY_ne_mlX : mlY ≠ mlX := by decide
@[simp] theorem ml_mlY_ne_mlR : mlY ≠ mlR := by decide
@[simp] theorem ml_mlY_ne_lKb : mlY ≠ lKb := by decide
@[simp] theorem ml_mlR_ne_mlP : mlR ≠ mlP := by decide
@[simp] theorem ml_mlR_ne_mlA : mlR ≠ mlA := by decide
@[simp] theorem ml_mlR_ne_mlB : mlR ≠ mlB := by decide
@[simp] theorem ml_mlR_ne_mlX : mlR ≠ mlX := by decide
@[simp] theorem ml_mlR_ne_mlY : mlR ≠ mlY := by decide
@[simp] theorem ml_mlR_ne_lKb : mlR ≠ lKb := by decide
@[simp] theorem ml_lKb_ne_mlP : lKb ≠ mlP := by decide
@[simp] theorem ml_lKb_ne_mlA : lKb ≠ mlA := by decide
@[simp] theorem ml_lKb_ne_mlB : lKb ≠ mlB := by decide
@[simp] theorem ml_lKb_ne_mlX : lKb ≠ mlX := by decide
@[simp] theorem ml_lKb_ne_mlY : lKb ≠ mlY := by decide
@[simp] theorem ml_lKb_ne_mlR : lKb ≠ mlR := by decide

/-- A heap list of memo nodes, newest first. -/
def MNodes (C : Ctx) (H : List (BitVec 64)) : BitVec 64 → List ((BitVec 64 × BitVec 64) × Bool) → Prop
  | p, [] => p = 0
  | p, ((a, b), v) :: xs => ∃ o nx, p = cellA C o ∧ o < C.HN ∧ H[o]? = some a ∧ H[o + 1]? = some b ∧
      H[o + 2]? = some (boolW v) ∧ H[o + 3]? = some nx ∧ MNodes C H nx xs

theorem mnodes_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (p : BitVec 64) (xs : List ((BitVec 64 × BitVec 64) × Bool)), MNodes C H p xs → MNodes C H' p xs
  | _, [], h => h
  | p, ((a, b), v) :: xs, ⟨o, nx, h1, h0, h2, h3, h4, h5, h6⟩ =>
    ⟨o, nx, h1, h0, pfx_get hp h2, pfx_get hp h3, pfx_get hp h4, pfx_get hp h5, mnodes_mono hp nx xs h6⟩

theorem mnodes_H {C : Ctx} {H H' : List (BitVec 64)} :
    ∀ {p : BitVec 64} {xs : List ((BitVec 64 × BitVec 64) × Bool)}, MNodes (ctxH C H') H p xs → MNodes C H p xs
  | _, [], h => h
  | _, ((_, _), _) :: xs, ⟨o, nx, h1, h0, h2, h3, h4, h5, h6⟩ => ⟨o, nx, h1, h0, h2, h3, h4, h5, mnodes_H h6⟩

def mlParams : List MlS := [mlP, mlA, mlB]
def mlLocals : List MlS := [mlX, mlY, mlR]

def mlMiss : ProgHOL 64 :=
  .seq (.assign .local mlX (.load .one (.op .add [vv mlP, .const 24])))
  (.seq (.call (some (some (.local, mlR), none)) fMl [vv mlX, vv mlA, vv mlB]) (.return (vv mlR)))

def mlCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv mlP) (.const 0)) (.return (.const 0))
  (.seq (.assign .local mlX (.load .one (vv mlP)))
  (.seq (.assign .local mlY (.load .one (.op .add [vv mlP, .const 8])))
  (.ite (.cmp .equal (vv mlX) (vv mlA))
    (.ite (.cmp .equal (vv mlY) (vv mlB))
      (.seq (.assign .local mlR (.load .one (.op .add [vv mlP, .const 16]))) (.return (.op .add [vv mlR, .const 1])))
      mlMiss)
    mlMiss)))

def mlBody : ProgHOL 64 := prologue mlLocals mlCore

section
variable {σ : Type}

theorem ml_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mlLocals → (ctxEnv C ++ mlParams.zip vals).get x = none :=
  Knot.params_none C mlLocals mlParams vals (by decide) (by decide)

/-- A word answer, nothing else changes. -/
def PostWV (C : Ctx) (s : AState) (o : Option Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = optWG boolW o ∧ SR C s st

theorem postWV_locals (C : Ctx) (s : AState) : ∀ (a : Option Bool) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostWV C s a w s' st → PostWV C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem ml_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)) (a b : BitVec 64) :
    ∀ (xs : List ((BitVec 64 × BitVec 64) × Bool)) (p : BitVec 64) (H : List (BitVec 64)) (s : AState),
      MNodes C H p xs →
      SpecR (σ := σ) (Pre (ctxH C H) s (mlParams.zip [p, a, b])) mlBody s (pure (xs.lookup (a, b)))
        (PostWV (ctxH C H) s) := by
  intro xs
  induction xs with
  | nil =>
    intro p H s hm
    have hp0 : p = 0 := hm
    subst hp0
    refine specR_prologue (postWV_locals _ _) (ml_none _ _) ?_
    unfold mlCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons x xs ih =>
    obtain ⟨⟨a', b'⟩, v⟩ := x
    intro p H s hm
    obtain ⟨o, nx, hpo, hoN, h0, h1, h2, h3, hrest⟩ := hm
    subst hpo
    have hne := ExSP.cellA_ne0 C hok o hoN
    refine specR_prologue (postWV_locals _ _) (ml_none _ _) ?_
    unfold mlCore
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) mlX (vv mlP) o a' h0 (by decide)
      (by simp +decide [Env.get, mlParams, ctxEnv]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mlY (.op .add [vv mlP, .const 8]) (o + 1) b' h1 (by decide)
      (by simp +decide [sev, Env.get, mlParams, ctxEnv]; exact cellA_add8 C o) ?_
    have hmiss : SpecR (σ := σ) (Inv (ctxH C H) s ((mlY, b') :: (mlX, a') :: (ctxEnv (ctxH C H) ++
        mlParams.zip [cellA C o, a, b])) [] (ctxLocals ++ mlLocals)) mlMiss s (pure (xs.lookup (a, b)))
        (PostWV (ctxH C H) s) := by
      unfold mlMiss
      refine UD.specR_heapLoadI' (C := ctxH C H) mlX (.op .add [vv mlP, .const 24]) (o + 3) nx h3 (by decide)
        (by simp +decide [sev, Env.get, mlParams, ctxEnv]; exact (show _ = cellA C (o + 3) by simpa using ExPre.cellA_off C o 3)) ?_
      refine specR_congr (m' := (pure (xs.lookup (a, b)) : AM (Option Bool)) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) mlR fMl mlParams [vv mlX, vv mlA, vv mlB] mlBody [nx, a, b]
        (by decide) rfl (by decide) hc
        ⟨by simp +decide [Env.get], by simp +decide [Env.get, mlParams, ctxEnv], by simp +decide [Env.get, mlParams, ctxEnv],
          trivial⟩
        (PostWV (ctxH C H) s) (fun r w s' H' => w = optWG boolW r ∧ s' = s ∧ H' = H)
        (fun r w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, h1, rfl⟩, by subst h1; exact h3⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk) (ih nx H s hrest))
        (fun r w s' H' _ ⟨hw, hs', hH'⟩ => ?_)
      subst hw hs' hH'
      exact specR_returnI _ (optWG boolW r) (by simp) (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases hab : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := hab
      have hl : (((a', b'), v) :: xs).lookup (a', b') = some v := by simp [List.lookup]
      rw [hl]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) mlR (.op .add [vv mlP, .const 16]) (o + 2) (boolW v) h2 (by decide)
        (by simp +decide [sev, Env.get, mlParams, ctxEnv]; exact (show _ = cellA C (o + 2) by simpa using ExPre.cellA_off C o 2)) ?_
      exact specR_returnI _ (boolW v + 1) (by simp +decide [sev, Env.get])
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hl : (((a', b'), v) :: xs).lookup (a, b) = xs.lookup (a, b) := by
        simp only [List.lookup]
        split
        · rename_i e; simp only [Prod.mk.injEq, beq_iff_eq] at e
          exact absurd ⟨e.1.symm, e.2.symm⟩ hab
        · rfl
      rw [hl]
      by_cases ha : a' = a
      · subst ha
        have hb : b' ≠ b := fun e => hab ⟨rfl, e⟩
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb])
          (fun h => absurd rfl h) (fun _ => hmiss)
      · exact specR_ifI _ 0 (by simp +decide [sev, Env.get, mlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ha])
          (fun h => absurd rfl h) (fun _ => hmiss)

end

end ConPanqueque.T.WC
