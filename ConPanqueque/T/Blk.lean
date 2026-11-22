import ConPanqueque.T.Loop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Blocks: list and array values in the heap

A value `xs : List (BitVec 64)` lives at image index `o` as the block `[n, x₀, …, xₙ₋₁]`; the value's
word is the block's address `cellA C o`. Blocks are immutable once built, so `BlkAt H o xs` survives
every extension of the image. A function returning a list states `PostA`: the result is a block of
some bigger image, and the caller continues at that image (`specR_call2IH`).
-/

namespace ConPanqueque.T

variable {σ : Type}

def BlkAt (H : List (BitVec 64)) (o : Nat) (xs : List (BitVec 64)) : Prop :=
  H[o]? = some (BitVec.ofNat 64 xs.length) ∧ ∀ i (hi : i < xs.length), H[o + 1 + i]? = some xs[i]

theorem blkAt_mono {H H' : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (hp : H <+: H') :
    BlkAt H' o xs := by
  obtain ⟨r, rfl⟩ := hp
  exact ⟨by rw [List.getElem?_append_left (by
      have := h.1; rcases Nat.lt_or_ge o H.length with hl | hl
      · exact hl
      · rw [List.getElem?_eq_none hl] at this; simp at this)]; exact h.1,
    fun i hi => by
      have h2 := h.2 i hi
      rw [List.getElem?_append_left (by
        rcases Nat.lt_or_ge (o + 1 + i) H.length with hl | hl
        · exact hl
        · rw [List.getElem?_eq_none hl] at h2; simp at h2)]; exact h2⟩

theorem blkAt_len {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) :
    o + 1 + xs.length ≤ H.length := by
  rcases xs.eq_nil_or_concat with e | ⟨ys, y, e⟩
  · subst e
    have := h.1; rcases Nat.lt_or_ge o H.length with hl | hl
    · simp; omega
    · rw [List.getElem?_eq_none hl] at this; simp at this
  · have h2 := h.2 (xs.length - 1) (by subst e; simp)
    rcases Nat.lt_or_ge (o + 1 + (xs.length - 1)) H.length with hl | hl
    · subst e; simp at hl ⊢; omega
    · rw [List.getElem?_eq_none hl] at h2; simp at h2

theorem blkAt_lt {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) : o < H.length := by
  have := blkAt_len h; omega

theorem blkAt_get {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (i : Nat)
    (hi : i < xs.length) : ∃ hl : o + 1 + i < H.length, H[o + 1 + i] = xs[i] := by
  have hl : o + 1 + i < H.length := by have := blkAt_len h; omega
  refine ⟨hl, ?_⟩
  have := h.2 i hi
  rw [List.getElem?_eq_getElem hl] at this; simpa using this

theorem blkAt_get0 {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) :
    ∃ hl : o < H.length, H[o] = BitVec.ofNat 64 xs.length := by
  have hl := blkAt_lt h
  refine ⟨hl, ?_⟩
  have := h.1
  rw [List.getElem?_eq_getElem hl] at this; simpa using this

/-- Setting an index outside the block keeps it. -/
theorem blkAt_set {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (j : Nat)
    (hj : j < o ∨ o + xs.length < j) (w : BitVec 64) : BlkAt (H.set j w) o xs :=
  ⟨by rw [List.getElem?_set_ne (by omega)]; exact h.1, fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact h.2 i hi⟩

/-- An `EIdx` list-returning function's post: the result is a block of a bigger image. -/
def PostA (C : Ctx) (xs : List EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (xs.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postA_locals (C : Ctx) : ∀ (a : List EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostA C a w s' st → PostA C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, hb, hs⟩ => ⟨H', o, hp, hw, hb, sr_of_eq hs rfl rfl rfl rfl⟩

theorem postA_sr {C : Ctx} {a : List EIdx} {w : BitVec 64} {s' : AState} {st : PState σ} (h : PostA C a w s' st) :
    SR C s' st := let ⟨_, _, hp, _, _, hs⟩ := h; sr_weakenH hs hp

/-- `x := f(e₁, e₂); rest` where the callee may grow the heap: the continuation runs at the image the
callee's post names. -/
theorem specR_call2IH {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 : MlS) (hne : p1 ≠ p2) (e1 e2 : ExpHOL 64) (B : ProgHOL 64) (v1 v2 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', C.H <+: H' ∧ Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) →
      u.locals.lookup p2 = some (.val (.word v2)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' H', C.H <+: H' → Qx a w s' H' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call2 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w H', C.H <+: H' ∧ Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    x f p1 p2 hne e1 e2 B (fun _ => v1) (fun _ => v2) (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨H', hp, hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, H', hp, hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w H', C.H <+: H' ∧ Qx a w s' H' ∧
      Inv (ctxH C H') s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, H', hp, hq, hu⟩ => hk a w s' H' hp hq u hu) t rfl

end ConPanqueque.T
