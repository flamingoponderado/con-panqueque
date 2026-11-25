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

/-! ## Inserting: one fresh node -/

def mlInsP (C : Ctx) (x : MlS) (ea eb ev ep : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 32)
  (.seq (.store (vv x) ea) (.seq (.store (.op .add [vv x, .const 8]) eb)
  (.seq (.store (.op .add [vv x, .const 16]) ev) (.seq (.store (.op .add [vv x, .const 24]) ep) rest))))

theorem specR_mlInsI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (ea eb ev ep : ExpHOL 64) (a b pw : BitVec 64) (v : Bool) (xs : List ((BitVec 64 × BitVec 64) × Bool))
    (hx : x ∈ D) (hea : ∀ w, sev ((x, w) :: Γ) ea = some a) (heb : ∀ w, sev ((x, w) :: Γ) eb = some b)
    (hev : ∀ w, sev ((x, w) :: Γ) ev = some (boolW v)) (hep : ∀ w, sev ((x, w) :: Γ) ep = some pw)
    (hm : MNodes C H pw xs)
    (hk : ∀ (H' : List (BitVec 64)) o, H <+: H' → MNodes C H' (cellA C o) (((a, b), v) :: xs) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (mlInsP C x ea eb ev ep rest) s m R := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) x (.const 32) 4 (by omega) hx (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hroom' : H1.length + 4 ≤ C.HN := hroom
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((x, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) ea H1.length (by show _ < (H1 ++ ws).length; simp; omega) a
    (by simp <;> rfl) (hea _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length a)) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv x, .const 8]) eb (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) b (by simp +decide [sev]; exact cellA_add8 C _) (heb _) ?_
  change SpecR (Inv (ctxH C (((H1 ++ ws).set H1.length a).set (H1.length + 1) b)) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv x, .const 16]) ev (H1.length + 2)
    (by show _ < (((H1 ++ ws).set _ _).set _ _).length; simp; omega) (boolW v)
    (by simp +decide [sev]; show cellA C H1.length + _ = cellA C (H1.length + 2); simpa using ExPre.cellA_off C H1.length 2)
    (hev _) ?_
  change SpecR (Inv (ctxH C ((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)))
    _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv x, .const 24]) ep (H1.length + 3)
    (by show _ < ((((H1 ++ ws).set _ _).set _ _).set _ _).length; simp; omega) pw
    (by simp +decide [sev]; show cellA C H1.length + _ = cellA C (H1.length + 3); simpa using ExPre.cellA_off C H1.length 3)
    (hep _) ?_
  change SpecR (Inv (ctxH C (((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
    (H1.length + 3) pw)) s ((x, cellA C H1.length) :: Γ) _ _) _ _ _ _
  have g0 : (((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
      (H1.length + 3) pw)[H1.length]? = some a := by simp [List.getElem?_set, hws]
  have g1 : (((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
      (H1.length + 3) pw)[H1.length + 1]? = some b := by simp [List.getElem?_set, hws]
  have g2 : (((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
      (H1.length + 3) pw)[H1.length + 2]? = some (boolW v) := by simp [List.getElem?_set, hws]
  have g3 : (((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
      (H1.length + 3) pw)[H1.length + 3]? = some pw := by simp [List.getElem?_set, hws]
  generalize hB4 : ((((H1 ++ ws).set H1.length a).set (H1.length + 1) b).set (H1.length + 2) (boolW v)).set
    (H1.length + 3) pw = B4 at g0 g1 g2 g3
  have hlen4 : B4.length = H1.length + 4 := by rw [← hB4]; simp [hws]
  have hpre : H <+: B4 := by
    rw [← hB4]
    exact prefix_set_ge (prefix_set_ge (prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _
      (by omega) _) _ (by omega) _) _ (by omega) _) _ (by omega) _
  exact hk B4 H1.length hpre ⟨H1.length, pw, rfl, by omega, g0, g1, g2, g3, mnodes_mono hpre pw xs hm⟩

/-! ## A `(handle, depth)`-keyed boolean memo -/

def WsRep (C : Ctx) (H : List (BitVec 64)) (p : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool) : Prop :=
  ∃ xs, MNodes C H p xs ∧ ∀ (h : EIdx) (d : Nat), d < 2 ^ 63 → memo[(h, d)]? = xs.lookup (Enc.idxW h, BitVec.ofNat 64 d)

theorem wsRep_empty (C : Ctx) (H : List (BitVec 64)) : WsRep C H 0 ∅ :=
  ⟨[], rfl, fun h d _ => by simp [List.lookup]⟩

theorem wsRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {p : BitVec 64}
    {memo : Std.HashMap (EIdx × Nat) Bool} (h : WsRep C H p memo) : WsRep C H' p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_mono hp p xs hm, he⟩

theorem wsRep_insert {C : Ctx} {H : List (BitVec 64)} {p p' : BitVec 64} {memo : Std.HashMap (EIdx × Nat) Bool}
    {xs : List ((BitVec 64 × BitVec 64) × Bool)} (he : ∀ (h : EIdx) (d : Nat), d < 2 ^ 63 → memo[(h, d)]? =
      xs.lookup (Enc.idxW h, BitVec.ofNat 64 d)) (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (r : Bool)
    (hm : MNodes C H p' (((Enc.idxW h, BitVec.ofNat 64 d), r) :: xs)) :
    WsRep C H p' (memo.insert (h, d) r) := by
  refine ⟨_, hm, fun h' d' hd' => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  simp only [List.lookup]
  by_cases e : (h, d) = (h', d')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    simp
  · rw [ite_eq_right (by simpa using e)]
    have : ¬ ((Enc.idxW h', BitVec.ofNat 64 d') == (Enc.idxW h, BitVec.ofNat 64 d)) = true := by
      simp only [beq_iff_eq, Prod.mk.injEq, not_and]
      intro e1 e2
      apply e
      rw [idxW_inj e1, (UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp e2]
    simp only [this]
    exact he h' d' hd'

theorem mnodes_toH {C : Ctx} {H H' : List (BitVec 64)} :
    ∀ {p : BitVec 64} {xs : List ((BitVec 64 × BitVec 64) × Bool)}, MNodes C H p xs → MNodes (ctxH C H') H p xs
  | _, [], h => h
  | _, ((_, _), _) :: xs, ⟨o, nx, h1, h0, h2, h3, h4, h5, h6⟩ => ⟨o, nx, h1, h0, h2, h3, h4, h5, mnodes_toH h6⟩

theorem wsRep_toH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap (EIdx × Nat) Bool}
    (h : WsRep C H p memo) : WsRep (ctxH C H') H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_toH hm, he⟩

theorem wsRep_ofH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap (EIdx × Nat) Bool}
    (h : WsRep (ctxH C H') H p memo) : WsRep C H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_H hm, he⟩

/-! ## A handle-keyed boolean memo, and a leaf list -/

def LbRep (C : Ctx) (H : List (BitVec 64)) (p : BitVec 64) (memo : Std.HashMap EIdx Bool) : Prop :=
  ∃ xs, MNodes C H p xs ∧ ∀ h : EIdx, memo[h]? = xs.lookup (Enc.idxW h, 0)

theorem lbRep_empty (C : Ctx) (H : List (BitVec 64)) : LbRep C H 0 ∅ :=
  ⟨[], rfl, fun h => by simp [List.lookup]⟩

theorem lbRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {p : BitVec 64}
    {memo : Std.HashMap EIdx Bool} (h : LbRep C H p memo) : LbRep C H' p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_mono hp p xs hm, he⟩

theorem lbRep_toH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap EIdx Bool}
    (h : LbRep C H p memo) : LbRep (ctxH C H') H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_toH hm, he⟩

theorem lbRep_ofH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap EIdx Bool}
    (h : LbRep (ctxH C H') H p memo) : LbRep C H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_H hm, he⟩

theorem lbRep_insert {C : Ctx} {H : List (BitVec 64)} {p' : BitVec 64} {memo : Std.HashMap EIdx Bool}
    {xs : List ((BitVec 64 × BitVec 64) × Bool)} (he : ∀ h : EIdx, memo[h]? = xs.lookup (Enc.idxW h, 0))
    (h : EIdx) (r : Bool) (hm : MNodes C H p' (((Enc.idxW h, 0), r) :: xs)) :
    LbRep C H p' (memo.insert h r) := by
  refine ⟨_, hm, fun h' => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  simp only [List.lookup]
  by_cases e : h = h'
  · subst e; simp
  · rw [ite_eq_right (by simpa using e)]
    have : ¬ ((Enc.idxW h', (0 : BitVec 64)) == (Enc.idxW h, 0)) = true := by
      simp only [beq_iff_eq, Prod.mk.injEq, and_true]
      intro e1; exact e (idxW_inj e1).symm
    simp only [this]
    exact he h'

def accEnc (it : Nat × EIdx) : (BitVec 64 × BitVec 64) × Bool := ((BitVec.ofNat 64 it.1, Enc.idxW it.2), false)

def AccRep (C : Ctx) (H : List (BitVec 64)) (p : BitVec 64) (acc : List (Nat × EIdx)) : Prop :=
  MNodes C H p (acc.map accEnc) ∧ ∀ it, it ∈ acc → it.1 < 2 ^ 64

theorem accRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {p : BitVec 64} {acc : List (Nat × EIdx)}
    (h : AccRep C H p acc) : AccRep C H' p acc :=
  ⟨mnodes_mono hp p _ h.1, h.2⟩

theorem leafMem_lookup (acc : List (Nat × EIdx)) (hs : ∀ it, it ∈ acc → it.1 < 2 ^ 64) (idx : Nat) (ty : EIdx)
    (hi : idx < 2 ^ 64) : leafMem acc idx ty = ((acc.map accEnc).lookup (BitVec.ofNat 64 idx, Enc.idxW ty)).isSome := by
  induction acc with
  | nil => rfl
  | cons it rest ih =>
    obtain ⟨i, t⟩ := it
    have hi' : i < 2 ^ 64 := hs (i, t) (by simp)
    simp only [leafMem, List.map_cons, accEnc, List.lookup]
    by_cases e : i = idx ∧ t = ty
    · obtain ⟨rfl, rfl⟩ := e; simp
    · have h1 : ¬ ((BitVec.ofNat 64 idx, Enc.idxW ty) == (BitVec.ofNat 64 i, Enc.idxW t)) = true := by
        simp only [beq_iff_eq, Prod.mk.injEq, not_and]
        intro e1 e2
        exact e ⟨((UD.ofNat_eq_iff_small _ _ hi hi').mp e1).symm, (idxW_inj e2).symm⟩
      simp only [h1]
      have h2 : (i == idx && t == ty) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        by_cases e3 : i = idx
        · exact Or.inr (fun e4 => e ⟨e3, e4⟩)
        · exact Or.inl e3
      rw [h2, Bool.false_or]
      exact ih (fun it hm => hs it (by simp [hm]))

/-! ## A seen set -/

def SeenRep (C : Ctx) (H : List (BitVec 64)) (p : BitVec 64) (seen : Std.HashMap EIdx Unit) : Prop :=
  ∃ xs, MNodes C H p xs ∧ ∀ h : EIdx, seen[h]? = (xs.lookup (Enc.idxW h, 0)).map (fun _ => ())

theorem seenRep_empty (C : Ctx) (H : List (BitVec 64)) : SeenRep C H 0 ∅ :=
  ⟨[], rfl, fun h => by simp [List.lookup]⟩

theorem seenRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {p : BitVec 64}
    {seen : Std.HashMap EIdx Unit} (h : SeenRep C H p seen) : SeenRep C H' p seen :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_mono hp p xs hm, he⟩

theorem seenRep_insert {C : Ctx} {H : List (BitVec 64)} {p' : BitVec 64} {seen : Std.HashMap EIdx Unit}
    {xs : List ((BitVec 64 × BitVec 64) × Bool)} (he : ∀ h : EIdx, seen[h]? = (xs.lookup (Enc.idxW h, 0)).map (fun _ => ()))
    (h : EIdx) (hm : MNodes C H p' (((Enc.idxW h, 0), true) :: xs)) :
    SeenRep C H p' (seen.insert h ()) := by
  refine ⟨_, hm, fun h' => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  simp only [List.lookup]
  by_cases e : h = h'
  · subst e; simp
  · rw [ite_eq_right (by simpa using e)]
    have : ¬ ((Enc.idxW h', (0 : BitVec 64)) == (Enc.idxW h, 0)) = true := by
      simp only [beq_iff_eq, Prod.mk.injEq, and_true]
      intro e1; exact e (idxW_inj e1).symm
    simp only [this]
    exact he h'

theorem accRep_cons {C : Ctx} {H : List (BitVec 64)} {p' : BitVec 64} {acc : List (Nat × EIdx)} (idx : Nat)
    (ty : EIdx) (hi : idx < 2 ^ 64) (hs : ∀ it, it ∈ acc → it.1 < 2 ^ 64)
    (hm : MNodes C H p' (((BitVec.ofNat 64 idx, Enc.idxW ty), false) :: acc.map accEnc)) :
    AccRep C H p' ((idx, ty) :: acc) :=
  ⟨hm, fun it h => by simp at h; rcases h with rfl | h; exact hi; exact hs it h⟩

end

end ConPanqueque.T.WC
