import ConPanqueque.Arena
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

namespace ConPanqueque.Rep

/-- Address `p + 8 i`. -/
def at8 (p : BitVec 64) (i : Nat) : BitVec 64 := p + BitVec.ofNat 64 (8 * i)

/-- `st (p + 8i) x₀; st (p + 8(i+1)) x₁; …` for the local `p` and locals `xs`. -/
def storeSeq (p : MlS) : List MlS → Nat → ProgHOL 64
  | [], _ => .skip
  | x :: xs, i => .seq (.store (.op .add [.var .local p, .const (BitVec.ofNat 64 (8 * i))]) (.var .local x))
      (storeSeq p xs (i + 1))

/-- The arena with the cells `p + 8(i+j) ↦ vⱼ` added. -/
def extSeq (h : Heap) (p : BitVec 64) : List (BitVec 64) → Nat → Heap
  | [], _ => h
  | v :: vs, i => extSeq (ext h (at8 p i) (.word v)) p vs (i + 1)

theorem storeSeq_spec {σ : Type} (pn : MlS) (p0 : BitVec 64) :
    ∀ (xs : List MlS) (vs : List (BitVec 64)) (i : Nat) (t : PanSemStateFiniteExact 64 σ) (h : Heap),
      ∀ (hlen : xs.length = vs.length),
      t.locals.lookup pn = some (.val (.word p0)) →
      (∀ j (hj : j < xs.length), t.locals.lookup xs[j] = some (.val (.word (vs[j]'(hlen ▸ hj))))) →
      InMem t h →
      (∀ j, j < xs.length → t.memaddrs (at8 p0 (i + j)) ∧ h (at8 p0 (i + j)) = none) →
      (∀ j k, j < xs.length → k < xs.length → j ≠ k → at8 p0 (i + j) ≠ at8 p0 (i + k)) →
      ∃ t', evaluateHOLFiniteState t (storeSeq pn xs i) = (none, t') ∧
        t'.locals = t.locals ∧ t'.memaddrs = t.memaddrs ∧ t'.topAddr = t.topAddr ∧
        InMem t' (extSeq h p0 vs i) ∧ Sub h (extSeq h p0 vs i)
  | [], [], i, t, h, _, _, _, hm, _, _ => ⟨t, by simp [storeSeq, evaluateHOLFiniteState_eq_evaluate_def],
      rfl, rfl, rfl, by simpa [extSeq] using hm, fun _ _ h => h⟩
  | x :: xs, v :: vs, i, t, h, hlen, hp, hx, hm, hfresh, hdist => by
    have hx0 := hx 0 (by simp)
    obtain ⟨hd0, hn0⟩ := hfresh 0 (by simp)
    simp at hx0 hd0 hn0
    let t1 := { t with memory := fun c => if c = at8 p0 i then HolWordLab.word v else t.memory c }
    have e1 : evaluateHOLFiniteState t (.store (.op .add [.var .local pn, .const (BitVec.ofNat 64 (8 * i))])
        (.var .local x)) = (none, t1) :=
      store_word t _ _ (at8 p0 i) v (by simp [evalHOLExact, evalListHOLExact, hp, at8, wordOpHOL, wordOp,
        valueIsWord, valueWord]) (by simp [evalHOLExact, hx0]) hd0
    have hm1 : InMem t1 (ext h (at8 p0 i) (.word v)) := inMem_store _ hm hn0 hd0
    obtain ⟨t', ev, hl, hd, ht, hm', hs'⟩ := storeSeq_spec pn p0 xs vs (i + 1) t1 (ext h (at8 p0 i) (.word v))
      (by simpa using hlen) (by simpa [t1] using hp)
      (fun j hj => by
        have := hx (j + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at this
        simpa [t1] using this)
      hm1
      (fun j hj => by
        obtain ⟨a, b⟩ := hfresh (j + 1) (by simp; omega)
        refine ⟨by simpa [t1, Nat.add_assoc, Nat.add_comm 1] using a, ?_⟩
        have hne : at8 p0 (i + 1 + j) ≠ at8 p0 i := by
          have := hdist (j + 1) 0 (by simp; omega) (by simp) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1] using this
        simp only [ext]; split
        · exact absurd ‹_› hne
        · simpa [Nat.add_assoc, Nat.add_comm 1] using b)
      (fun j k hj hk hjk => by
        have := hdist (j + 1) (k + 1) (by simp; omega) (by simp; omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    refine ⟨t', ?_, by simpa [t1] using hl, by simpa [t1] using hd, by simpa [t1] using ht, by simpa [extSeq] using hm',
      fun a w ha => hs' a w (sub_ext _ hn0 a w ha)⟩
    simp only [storeSeq]
    rw [seq_normal _ e1, ev]

end ConPanqueque.Rep
