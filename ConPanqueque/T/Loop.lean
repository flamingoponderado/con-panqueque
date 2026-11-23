import ConPanqueque.T.Heap
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Loops over the invariant

`Step P c Q`: running `c` from a `P` state stops or finishes normally in a `Q` state (the twin does
nothing). Loop bodies are built from step combinators; `specR_forI` runs a counted `while` whose
`i`-th iteration moves `Inv (K i) s (G i)` to `Inv (K (i+1)) s (G (i+1))`.
-/

namespace ConPanqueque.T

variable {σ : Type}

def Step (P : PState σ → Prop) (c : ProgHOL 64) (Q : PState σ → Prop) : Prop :=
  ∀ t, P t → Stop (evaluateHOLFiniteState t c).1 ∨
    ((evaluateHOLFiniteState t c).1 = none ∧ Q (evaluateHOLFiniteState t c).2)

theorem specR_step {α : Type} {P Q : PState σ → Prop} {c rest : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h1 : Step P c Q) (h2 : SpecR Q rest s m R) :
    SpecR P (.seq c rest) s m R := specR_seq h1 h2

theorem step_seq {P Q Q' : PState σ → Prop} {c1 c2 : ProgHOL 64} (h1 : Step P c1 Q) (h2 : Step Q c2 Q') :
    Step P (.seq c1 c2) Q' := by
  intro t ht
  rcases h1 t ht with hs | ⟨hn, hq⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  have e : evaluateHOLFiniteState t c1 = (none, (evaluateHOLFiniteState t c1).2) := by rw [← hn]
  rw [seq_normal _ e]; exact h2 _ hq

theorem step_mono {P P' Q Q' : PState σ → Prop} {c : ProgHOL 64} (h : Step P c Q) (hP : ∀ t, P' t → P t)
    (hQ : ∀ t, Q t → Q' t) : Step P' c Q' := by
  intro t ht
  rcases h t (hP t ht) with hs | ⟨hn, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn, hQ _ hq⟩

theorem step_assignI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64)
    (v : BitVec 64) (hx : x ∈ D) (he : sev Γ e = some v) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x e) (Inv C s ((x, v) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, h0⟩ := ht.decl x hx
  rw [ConsLoop.assign_local t x e v w0 (inv_ev ht he) h0]
  exact Or.inr ⟨rfl, inv_set ht x v⟩

theorem step_loadI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64)
    (a v : BitVec 64) (hx : x ∈ D) (he : sev Γ e = some a) (hm : (a, v) ∈ M) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, v) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, h0⟩ := ht.decl x hx
  rw [ConsLoop.assign_local t x _ v w0
    (by rw [eval_load_word t _ _ (inv_ev ht he) (ht.mem a v hm).1, (ht.mem a v hm).2]) h0]
  exact Or.inr ⟨rfl, inv_set ht x _⟩

theorem step_heapLoadI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64)
    (j : Nat) (hj : j < C.H.length) (hx : x ∈ D) (he : sev Γ e = some (cellA C j)) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, C.H[j]) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, h0⟩ := ht.decl x hx
  rw [ConsLoop.assign_local t x _ C.H[j] w0
    (by rw [eval_load_word t _ _ (inv_ev ht he) (heap_cell ht.sr j hj).1, (heap_cell ht.sr j hj).2]) h0]
  exact Or.inr ⟨rfl, inv_set ht x _⟩

theorem step_heapStoreI {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (ea ev : ExpHOL 64) (j : Nat) (hj : j < C.H.length) (w : BitVec 64) (hea : sev Γ ea = some (cellA C j))
    (hev : sev Γ ev = some w) :
    Step (Inv (σ := σ) C s Γ M D) (.store ea ev) (Inv (ctxH C (C.H.set j w)) s Γ [] D) := by
  intro t ht
  rw [store_word t ea ev _ w (inv_ev ht hea) (inv_ev ht hev) (heap_cell ht.sr j hj).1]
  exact Or.inr ⟨rfl, sr_heapStore hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun _ _ h => absurd h (by simp),
    ht.decl⟩

theorem inv_decClock {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) : Inv C s Γ M D (decClockHOLFinite t) :=
  ⟨sr_of_eq h.sr rfl rfl rfl rfl, h.env, h.mem, h.decl⟩

/-- A counted loop: iteration `i < n` moves the `i`-th invariant to the next; the test is nonzero
exactly below `n`. -/
theorem specR_forI {α : Type} {s : AState} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    {D : List MlS} {M : Mem} (c : ExpHOL 64) (body rest : ProgHOL 64) (n : Nat) (K : Nat → Ctx) (G : Nat → Env)
    (hc : ∀ i, i ≤ n → ∃ w, sev (G i) c = some w ∧ (w ≠ 0 ↔ i < n))
    (hb : ∀ i, i < n → Step (Inv (σ := σ) (K i) s (G i) M D) body (Inv (K (i + 1)) s (G (i + 1)) M D))
    (hr : SpecR (Inv (K n) s (G n) M D) rest s m R) :
    SpecR (Inv (K 0) s (G 0) M D) (.seq (.while c body) rest) s m R := by
  refine specR_seq (fun t ht => ?_) hr
  have W := while_stop (σ := σ) c body (fun u => ∃ i, i ≤ n ∧ Inv (K i) s (G i) M D u) (Inv (K n) s (G n) M D)
    (by
      intro u hu
      obtain ⟨i, hi, hu⟩ := hu
      obtain ⟨w, hw, hiff⟩ := hc i hi
      refine ⟨w, ?_, fun h0 => ?_, fun hn _ => ?_⟩
      · simp only [evalHOLFinite]; exact inv_ev hu hw
      · have : i = n := by
          rcases Nat.lt_or_ge i n with hlt | hge
          · exact absurd h0 (hiff.mpr hlt)
          · omega
        subst this; exact hu
      · have hlt := hiff.mp hn
        rcases hb i hlt _ (inv_decClock hu) with hs | ⟨hn', hq⟩
        · exact Or.inl hs
        · exact Or.inr ⟨hn', i + 1, by omega, hq⟩)
  exact W t ⟨0, Nat.zero_le _, ht⟩

/-- The counted loop as a `Step` (for a loop nested in another loop's body). -/
theorem step_forI {D : List MlS} {M : Mem} {s : AState} (c : ExpHOL 64) (body : ProgHOL 64) (n : Nat)
    (K : Nat → Ctx) (G : Nat → Env)
    (hc : ∀ i, i ≤ n → ∃ w, sev (G i) c = some w ∧ (w ≠ 0 ↔ i < n))
    (hb : ∀ i, i < n → Step (Inv (σ := σ) (K i) s (G i) M D) body (Inv (K (i + 1)) s (G (i + 1)) M D)) :
    Step (Inv (σ := σ) (K 0) s (G 0) M D) (.while c body) (Inv (K n) s (G n) M D) := by
  intro t ht
  exact while_stop (σ := σ) c body (fun u => ∃ i, i ≤ n ∧ Inv (K i) s (G i) M D u) (Inv (K n) s (G n) M D)
    (by
      intro u hu
      obtain ⟨i, hi, hu⟩ := hu
      obtain ⟨w, hw, hiff⟩ := hc i hi
      refine ⟨w, ?_, fun h0 => ?_, fun hn _ => ?_⟩
      · simp only [evalHOLFinite]; exact inv_ev hu hw
      · have : i = n := by
          rcases Nat.lt_or_ge i n with hlt | hge
          · exact absurd h0 (hiff.mpr hlt)
          · omega
        subst this; exact hu
      · have hlt := hiff.mp hn
        rcases hb i hlt _ (inv_decClock hu) with hs | ⟨hn', hq⟩
        · exact Or.inl hs
        · exact Or.inr ⟨hn', i + 1, by omega, hq⟩) t ⟨0, Nat.zero_le _, ht⟩

end ConPanqueque.T
