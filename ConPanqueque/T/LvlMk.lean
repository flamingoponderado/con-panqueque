import ConPanqueque.T.LvlEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Building small blocks

`alloc3 C x e₀ e₁ e₂ rest`: allocate three words, store the three values, continue with the block's
address in `x`; likewise for one and two words. The continuation runs at the image holding the block.
-/

namespace ConPanqueque.T

variable {σ : Type}

def alloc3 (C : Ctx) (x : MlS) (e0 e1 e2 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 24) (.seq (.store (vv x) e0)
    (.seq (.store (.op .add [vv x, .const 8]) e1) (.seq (.store (.op .add [vv x, .const 16]) e2) rest)))

def alloc2 (C : Ctx) (x : MlS) (e0 e1 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 16) (.seq (.store (vv x) e0) (.seq (.store (.op .add [vv x, .const 8]) e1) rest))

def alloc1 (C : Ctx) (x : MlS) (e0 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 8) (.seq (.store (vv x) e0) rest)

theorem cellA_add_ofNat (C : Ctx) (o k : Nat) : cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := by
  simp only [cellA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem specR_alloc3I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 e2 : ExpHOL 64) (w0 w1 w2 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (h2 : ∀ v, sev ((x, v) :: Γ) e2 = some w2)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 3 →
      SpecR (Inv (ctxH C ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2)) s
        ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc3 C x e0 e1 e2 rest) s m R := by
  unfold alloc3
  refine specR_allocI x _ 3 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  have hl : ∀ k, k < 3 → H2.length + k < (H2 ++ ws).length := by intro k hk; simp [hws]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (hl 0 (by decide)) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e2 (H2.length + 2) (by simp [ctxH, hws]) w2
    (by simp [sev]; exact cellA_add_ofNat C H2.length 2) (h2 _) ?_
  exact hk H2 ws hp hws

theorem specR_alloc2I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 : ExpHOL 64) (w0 w1 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 2 →
      SpecR (Inv (ctxH C (((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1)) s
        ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc2 C x e0 e1 rest) s m R := by
  unfold alloc2
  refine specR_allocI x _ 2 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  have hl : ∀ k, k < 2 → H2.length + k < (H2 ++ ws).length := by intro k hk; simp [hws]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (hl 0 (by decide)) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  exact hk H2 ws hp hws

theorem specR_alloc1I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 : ExpHOL 64) (w0 : BitVec 64) (hx : x ∈ D) (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 1 →
      SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length w0)) s ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc1 C x e0 rest) s m R := by
  unfold alloc1
  refine specR_allocI x _ 1 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (by simp [ctxH, hws]) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  exact hk H2 ws hp hws

theorem img_prefix (H2 : List (BitVec 64)) (B : List (BitVec 64)) (hl : H2.length ≤ B.length)
    (hg : ∀ k, k < H2.length → B[k]? = H2[k]?) : H2 <+: B := prefix_of_get? hl hg

section
variable (H2 ws : List (BitVec 64)) (w0 w1 w2 : BitVec 64)

theorem img3_get (h : ws.length = 3) :
    ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2)[H2.length]? = some w0 ∧
    ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2)[H2.length + 1]? = some w1 ∧
    ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2)[H2.length + 2]? = some w2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.getElem?_set, h]

theorem img3_prefix (h : ws.length = 3) :
    H2 <+: ((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2) :=
  img_prefix _ _ (by simp [h]) (fun k hk => by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_append_left hk])

theorem img2_get (h : ws.length = 2) :
    (((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1)[H2.length]? = some w0 ∧
    (((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1)[H2.length + 1]? = some w1 := by
  refine ⟨?_, ?_⟩ <;> simp [List.getElem?_set, h]

theorem img2_prefix (h : ws.length = 2) : H2 <+: (((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1) :=
  img_prefix _ _ (by simp [h]) (fun k hk => by
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_append_left hk])

theorem img1_get (h : ws.length = 1) : ((H2 ++ ws).set H2.length w0)[H2.length]? = some w0 := by
  simp [List.getElem?_set, h]

theorem img1_prefix (h : ws.length = 1) : H2 <+: ((H2 ++ ws).set H2.length w0) :=
  img_prefix _ _ (by simp [h]) (fun k hk => by
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk])

end

/-! ## The level blocks -/

theorem lrep_mkMax (C : Ctx) (ls : LStore) (H2 ws : List (BitVec 64)) (wu wv : BitVec 64) (u v : ConLeche.Level)
    (h3 : ws.length = 3) (hp : C.H <+: H2) (hu : LRep C.HB C.H ls wu u) (hv : LRep C.HB C.H ls wv v) (tag : Nat)
    (ht : tag = 2) :
    LRep C.HB ((((H2 ++ ws).set H2.length (BitVec.ofNat 64 tag)).set (H2.length + 1) wu).set (H2.length + 2) wv) ls
      (cellA C H2.length) (.max u v) := by
  subst ht
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (BitVec.ofNat 64 2) wu wv h3
  have hp' := hp.trans (img3_prefix H2 ws (BitVec.ofNat 64 2) wu wv h3)
  exact Or.inr ⟨H2.length, wu, wv, rfl, g0, g1, g2, lrep_mono hp' u wu hu, lrep_mono hp' v wv hv⟩

theorem lrep_mkImax (C : Ctx) (ls : LStore) (H2 ws : List (BitVec 64)) (wu wv : BitVec 64) (u v : ConLeche.Level)
    (h3 : ws.length = 3) (hp : C.H <+: H2) (hu : LRep C.HB C.H ls wu u) (hv : LRep C.HB C.H ls wv v) :
    LRep C.HB ((((H2 ++ ws).set H2.length (BitVec.ofNat 64 3)).set (H2.length + 1) wu).set (H2.length + 2) wv) ls
      (cellA C H2.length) (.imax u v) := by
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (BitVec.ofNat 64 3) wu wv h3
  have hp' := hp.trans (img3_prefix H2 ws (BitVec.ofNat 64 3) wu wv h3)
  exact Or.inr ⟨H2.length, wu, wv, rfl, g0, g1, g2, lrep_mono hp' u wu hu, lrep_mono hp' v wv hv⟩

theorem lrep_mkSucc (C : Ctx) (ls : LStore) (H2 ws : List (BitVec 64)) (wu : BitVec 64) (u : ConLeche.Level)
    (h2 : ws.length = 2) (hp : C.H <+: H2) (hu : LRep C.HB C.H ls wu u) :
    LRep C.HB (((H2 ++ ws).set H2.length (BitVec.ofNat 64 1)).set (H2.length + 1) wu) ls
      (cellA C H2.length) (.succ u) := by
  obtain ⟨g0, g1⟩ := img2_get H2 ws (BitVec.ofNat 64 1) wu h2
  have hp' := hp.trans (img2_prefix H2 ws (BitVec.ofNat 64 1) wu h2)
  exact Or.inr ⟨H2.length, wu, rfl, g0, g1, lrep_mono hp' u wu hu⟩

theorem lrep_mkParam (C : Ctx) (ls : LStore) (H2 ws : List (BitVec 64)) (nh : NIdx) (f : Nat) (n : ConLeche.Name)
    (h2 : ws.length = 2) (hd : denoteNAux ls.ns f nh = some n) :
    LRep C.HB (((H2 ++ ws).set H2.length (BitVec.ofNat 64 4)).set (H2.length + 1) (Enc.idxW nh)) ls
      (cellA C H2.length) (.param n) := by
  obtain ⟨g0, g1⟩ := img2_get H2 ws (BitVec.ofNat 64 4) (Enc.idxW nh) h2
  exact Or.inr ⟨H2.length, nh, f, rfl, g0, g1, hd⟩

theorem lrep_mkZero (C : Ctx) (ls : LStore) (H2 ws : List (BitVec 64)) (h1 : ws.length = 1) :
    LRep C.HB ((H2 ++ ws).set H2.length (BitVec.ofNat 64 0)) ls (cellA C H2.length) .zero :=
  Or.inr ⟨H2.length, rfl, img1_get H2 ws _ h1⟩

end ConPanqueque.T
