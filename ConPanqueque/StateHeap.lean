import ConPanqueque.Node
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons ConPanqueque.Tail
open ConPanqueque.Node

/-!
# The arena as a function of the state

For allocating recursions the heap grows between calls, and a call's result
pointer is not known in advance. So the arena heap is read off the state:
`hOf s lo hp` is the memory on `[lo, hp)`. `AInv s lo hp` is the arena invariant
(the global `hp`, the arena's addresses, the free region above it), and
`Grows s st lo hp hp'`: `st`'s arena extends `s`'s (memory below `hp` kept), so
everything represented in `s`'s arena still is in `st`'s (`grows_sub`).
`mkNode_ainv` is `mkNode_spec` in these terms.
-/

namespace ConPanqueque.StateHeap

def hOf {σ : Type} (s : PanSemStateFiniteExact 64 σ) (lo hp : BitVec 64) : Heap :=
  fun a => if lo ≤ a ∧ a < hp then some (s.memory a) else none

structure AInv {σ : Type} (s : PanSemStateFiniteExact 64 σ) (lo hp : BitVec 64) : Prop where
  hpv : s.globals.lookup nHp = some (.val (.word hp))
  le : lo ≤ hp
  pos : lo ≠ 0
  mem : ∀ a, lo ≤ a → a < hp → s.memaddrs a
  free : Free s hp

theorem ainv_arena {σ : Type} {s : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} (hi : AInv s lo hp) :
    ArenaInv s (hOf s lo hp) hp := by
  refine ⟨?_, hi.free, ?_⟩
  · intro a w ha
    simp only [hOf] at ha
    split at ha
    · rename_i hh; cases ha; exact ⟨hi.mem a hh.1 hh.2, rfl⟩
    · cases ha
  · intro a w ha
    simp only [hOf] at ha
    split at ha
    · rename_i hh; exact hh.2
    · cases ha

theorem hOf_pos {σ : Type} {s : PanSemStateFiniteExact 64 σ} {lo hp a : BitVec 64} {w : HolWordLab 64}
    (hi : AInv s lo hp) (ha : hOf s lo hp a = some w) : a ≠ 0 := by
  simp only [hOf] at ha
  split at ha
  · rename_i hh; intro e; subst e; exact hi.pos (by have := hh.1; bv_omega)
  · cases ha

/-- `st`'s arena extends `s`'s. -/
structure Grows {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (lo hp hp' : BitVec 64) : Prop where
  le : hp ≤ hp'
  mem : ∀ a, lo ≤ a → a < hp → st.memory a = s.memory a

theorem grows_sub {σ : Type} {s st : PanSemStateFiniteExact 64 σ} {lo hp hp' : BitVec 64}
    (g : Grows s st lo hp hp') : Sub (hOf s lo hp) (hOf st lo hp') := by
  intro a w ha
  simp only [hOf] at ha ⊢
  split at ha
  · rename_i hh
    have h2 : a < hp' := by have := g.le; have := hh.2; bv_omega
    simp only [hh.1, h2, and_self, ↓reduceIte]; rw [g.mem a hh.1 hh.2]; exact ha
  · cases ha

theorem grows_refl {σ : Type} (s : PanSemStateFiniteExact 64 σ) (lo hp : BitVec 64) : Grows s s lo hp hp :=
  ⟨BitVec.le_refl _, fun _ _ _ => rfl⟩

theorem grows_trans {σ : Type} {s t u : PanSemStateFiniteExact 64 σ} {lo h1 h2 h3 : BitVec 64}
    (g1 : Grows s t lo h1 h2) (g2 : Grows t u lo h2 h3) : Grows s u lo h1 h3 :=
  ⟨by have := g1.le; have := g2.le; bv_omega,
   fun a ha hb => by rw [g2.mem a ha (by have := g1.le; bv_omega), g1.mem a ha hb]⟩

/-- Same memory, address space and globals: same arena. -/
theorem ainv_of_eq {σ : Type} {s t : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} (hi : AInv s lo hp)
    (hg : t.globals = s.globals) (hd : t.memaddrs = s.memaddrs) (ht : t.topAddr = s.topAddr) : AInv t lo hp :=
  ⟨by rw [hg]; exact hi.hpv, hi.le, hi.pos, fun a h1 h2 => by rw [hd]; exact hi.mem a h1 h2,
   ⟨by rw [ht]; exact hi.free.1, fun a h1 h2 => by rw [hd]; exact hi.free.2 a h1 (by rw [← ht]; exact h2)⟩⟩

theorem hOf_of_eq {σ : Type} {s t : PanSemStateFiniteExact 64 σ} (lo hp : BitVec 64) (hm : t.memory = s.memory) :
    hOf t lo hp = hOf s lo hp := by
  funext a; simp only [hOf, hm]

/-- `mkNode` in arena-state form. -/
theorem mkNode_ainv {σ : Type} (t : PanSemStateFiniteExact 64 σ) (lo hp tag dv : BitVec 64)
    (dexp : ExpHOL 64) (fs : List MlS) (ws : List (BitVec 64)) (hlen : fs.length = ws.length)
    (hnD : nD ∉ fs) (hnT : nTg ∉ fs) (hnP : nP ∉ fs) (hsmall : 8 * (fs.length + 2) < 2 ^ 64)
    (hd : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dexp =
      some (.val (.word dv)))
    (hx : ∀ j (hj : j < fs.length), t.locals.lookup fs[j] = some (.val (.word (ws[j]'(hlen ▸ hj)))))
    (hi : AInv t lo hp) :
    Stop (evaluateHOLFiniteState t (mkNode tag dexp fs)).1 ∨
      let st := (evaluateHOLFiniteState t (mkNode tag dexp fs)).2
      let hp' := hp + BitVec.ofNat 64 (8 * (fs.length + 2))
      (evaluateHOLFiniteState t (mkNode tag dexp fs)).1 = some (.returned (.val (.word hp))) ∧
        AInv st lo hp' ∧ Grows t st lo hp hp' ∧ hp ≠ 0 ∧
        (∀ j (hj : j < fs.length + 2), hOf st lo hp' (at8 hp j) = some (.word ((tag :: dv :: ws)[j]'(by simp [← hlen]; omega)))) ∧
        st.code = t.code ∧ st.clock = t.clock ∧ (∀ g, g ≠ nHp → st.globals.lookup g = t.globals.lookup g) := by
  rcases mkNode_spec t (hOf t lo hp) hp tag dv dexp fs ws hlen hnD hnT hnP hsmall hd hx hi.hpv (ainv_arena hi) with
    hs | ⟨h', hr, ok⟩
  · exact Or.inl hs
  right
  intro st hp'
  have n8 : (BitVec.ofNat 64 (8 * (fs.length + 2))).toNat = 8 * (fs.length + 2) := by simp; omega
  -- no wrap-around: the first cell is below the new heap pointer
  have c0 := ok.cells 0 (by simp)
  have b0 := ok.arena.2.2 _ _ c0
  have hnw : hp.toNat + 8 * (fs.length + 2) < 2 ^ 64 := by
    simp only [at8] at b0; bv_omega
  have hle : hp ≤ hp' := by simp only [hp']; bv_omega
  have hpos : hp ≠ 0 := by have := hi.le; have := hi.pos; bv_omega
  have hj8 : ∀ j, j < fs.length + 2 → hp ≤ at8 hp j ∧ at8 hp j < hp' := by
    intro j hj; simp only [at8, hp']
    have : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by simp; omega
    constructor <;> bv_omega
  refine ⟨hr, ⟨ok.hp, by have := hi.le; bv_omega, hi.pos, ?_, ok.arena.2.1⟩, ⟨hle, ?_⟩, hpos, ?_,
    ok.code, ok.clock, ok.globals⟩
  · intro a h1 h2
    rw [ok.memaddrs]
    by_cases ha : a < hp
    · exact hi.mem a h1 ha
    · have := ok.arena.2.1.1
      rw [ok.topAddr] at this
      simp only [hp'] at h2
      exact hi.free.2 a (by bv_omega) (by bv_omega)
  · intro a h1 h2
    exact ok.memory a (fun j hj e => by have := (hj8 j hj).1; subst e; bv_omega)
  · intro j hj
    have cj := ok.cells j (by simp; omega)
    have mj := (ok.arena.1 _ _ cj).2
    have c1 : lo ≤ at8 hp j := by have := hi.le; have := (hj8 j hj).1; bv_omega
    simp only [hOf, c1, (hj8 j hj).2, and_self, ↓reduceIte]
    exact congrArg some mj

end ConPanqueque.StateHeap
