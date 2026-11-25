import ConPanqueque.Tail
import ConPanqueque.Logic.Stop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons ConPanqueque.Tail

/-!
# A guarded node constructor of any shape

`mkNode tag dexp fs` checks that the arena has room for `|fs| + 2` words (else it
`hang`s: the program stops without a verdict), computes the data word `dexp`,
and writes the block `[tag, data, fs…]`. `mkNode_spec`: it stops, or it returns
the fresh block, with the arena invariant re-established, and nothing else
changed (code, clock, address space, the other globals, memory outside the block).
-/

namespace ConPanqueque.Node

def guardN (n : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.const n)) hang .skip

def mkNode (tag : BitVec 64) (dexp : ExpHOL 64) (fs : List MlS) : ProgHOL 64 :=
  .seq (guardN (BitVec.ofNat 64 (8 * (fs.length + 2))))
    (.dec nD .one dexp (.dec nTg .one (.const tag) (tailN (nTg :: nD :: fs))))

/-- What `mkNode` guarantees when it returns. -/
structure NodeOk {σ : Type} (t st : PanSemStateFiniteExact 64 σ) (h h' : Heap) (p0 : BitVec 64) (n : Nat)
    (cells : List (BitVec 64)) : Prop where
  arena : ArenaInv st h' (p0 + BitVec.ofNat 64 (8 * n))
  sub : Sub h h'
  cells : ∀ j (hj : j < cells.length), h' (at8 p0 j) = some (.word cells[j])
  hp : st.globals.lookup nHp = some (.val (.word (p0 + BitVec.ofNat 64 (8 * n))))
  code : st.code = t.code
  clock : st.clock = t.clock
  memaddrs : st.memaddrs = t.memaddrs
  topAddr : st.topAddr = t.topAddr
  globals : ∀ g, g ≠ nHp → st.globals.lookup g = t.globals.lookup g
  memory : ∀ c, (∀ j, j < n → c ≠ at8 p0 j) → st.memory c = t.memory c

theorem mkNode_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (p0 tag dv : BitVec 64)
    (dexp : ExpHOL 64) (fs : List MlS) (ws : List (BitVec 64)) (hlen : fs.length = ws.length)
    (hnD : nD ∉ fs) (hnT : nTg ∉ fs) (hnP : nP ∉ fs) (hsmall : 8 * (fs.length + 2) < 2 ^ 64)
    (hd : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dexp =
      some (.val (.word dv)))
    (hx : ∀ j (hj : j < fs.length), t.locals.lookup fs[j] = some (.val (.word (ws[j]'(hlen ▸ hj)))))
    (hhp : t.globals.lookup nHp = some (.val (.word p0))) (hi : ArenaInv t h p0) :
    Stop (evaluateHOLFiniteState t (mkNode tag dexp fs)).1 ∨
      ∃ h', (evaluateHOLFiniteState t (mkNode tag dexp fs)).1 = some (.returned (.val (.word p0))) ∧
        NodeOk t (evaluateHOLFiniteState t (mkNode tag dexp fs)).2 h h' p0 (fs.length + 2) (tag :: dv :: ws) := by
  let n8 := BitVec.ofNat 64 (8 * (fs.length + 2))
  have hg : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.const n8)) =
      some (.val (.word (if t.topAddr - p0 < n8 then 1 else 0))) := by
    simp [evalHOLExact, evalListHOLExact, hhp, wordOpHOL, wordOp, valueIsWord, valueWord,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  unfold mkNode guardN
  by_cases hfull : t.topAddr - p0 < n8
  · left
    apply seq_stop
    rw [ite_word t _ _ _ _ hg]; simp only [hfull, ↓reduceIte]
    split
    · exact hang_stop t
    · rename_i hh; exact absurd (by decide) hh
  right
  have eg : evaluateHOLFiniteState t (.ite (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.const n8)) hang .skip)
      = (none, t) := by
    rw [ite_word t _ _ _ _ hg]; simp only [hfull, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    · rw [evaluateHOLFiniteState_eq_evaluate_def]
  rw [seq_normal _ eg]
  let t1 := setVarHOLFinite nD (.val (.word dv)) t
  let t2 := setVarHOLFinite nTg (.val (.word tag)) t1
  have l2 : ∀ x, x ∈ fs → t2.locals.lookup x = t.locals.lookup x := by
    intro x hx'
    simp only [t2, t1]
    rw [lookup_setVar_other _ _ (by rintro rfl; exact hnT hx'), lookup_setVar_other _ _ (by rintro rfl; exact hnD hx')]
  obtain ⟨h', r1, ⟨a1, a2, a3⟩, sub, cells, hp, cd, ck, ma, ta, gl, mm⟩ :=
    tailN_spec t2 h p0 (nTg :: nD :: fs) (tag :: dv :: ws) (by simp [hlen])
      (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hnP⟩) (by simpa using hsmall)
      (fun j hj => by
        match j, hj with
        | 0, _ => simp [t2]
        | 1, _ =>
          simp only [t2, t1, List.getElem_cons_succ, List.getElem_cons_zero]
          rw [lookup_setVar_other _ _ (by decide)]; simp
        | j + 2, hj =>
          simp only [List.getElem_cons_succ]
          rw [l2 _ (List.getElem_mem _)]; exact hx j (by simp at hj; omega))
      (by simpa [t2, t1, setVarHOLFinite] using hhp)
      ⟨inMem_of_eq rfl rfl hi.1, by simpa [t2, t1, setVarHOLFinite, Free] using hi.2.1, hi.2.2⟩
      (by simpa [t2, t1, setVarHOLFinite] using hfull)
  obtain ⟨L2, e2⟩ := dec_word' t1 nTg (.const tag) tag (tailN (nTg :: nD :: fs)) (by simp [evalHOLExact])
  obtain ⟨L1, e1⟩ := dec_word' t nD dexp dv (.dec nTg .one (.const tag) (tailN (nTg :: nD :: fs))) hd
  rw [e1, e2]
  refine ⟨h', r1, ⟨⟨inMem_of_eq rfl rfl a1, a2, a3⟩, sub, fun j hj => cells j (by simp [hlen] at hj ⊢; omega),
    hp, cd, ck, ma, ta, fun g hg' => gl g hg', fun c hc => mm c (by simpa using hc)⟩⟩

/-- A raw block `[fs…]` (no tag or data word), guarded like `mkNode`. -/
def mkCell (fs : List MlS) : ProgHOL 64 :=
  .seq (guardN (BitVec.ofNat 64 (8 * fs.length))) (tailN fs)

theorem mkCell_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (p0 : BitVec 64)
    (fs : List MlS) (ws : List (BitVec 64)) (hlen : fs.length = ws.length)
    (hnP : nP ∉ fs) (hsmall : 8 * fs.length < 2 ^ 64)
    (hx : ∀ j (hj : j < fs.length), t.locals.lookup fs[j] = some (.val (.word (ws[j]'(hlen ▸ hj)))))
    (hhp : t.globals.lookup nHp = some (.val (.word p0))) (hi : ArenaInv t h p0) :
    Stop (evaluateHOLFiniteState t (mkCell fs)).1 ∨
      ∃ h', (evaluateHOLFiniteState t (mkCell fs)).1 = some (.returned (.val (.word p0))) ∧
        NodeOk t (evaluateHOLFiniteState t (mkCell fs)).2 h h' p0 fs.length ws := by
  let n8 := BitVec.ofNat 64 (8 * fs.length)
  have hg : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.const n8)) =
      some (.val (.word (if t.topAddr - p0 < n8 then 1 else 0))) := by
    simp [evalHOLExact, evalListHOLExact, hhp, wordOpHOL, wordOp, valueIsWord, valueWord,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  unfold mkCell guardN
  by_cases hfull : t.topAddr - p0 < n8
  · left
    apply seq_stop
    rw [ite_word t _ _ _ _ hg]; simp only [hfull, ↓reduceIte]
    split
    · exact hang_stop t
    · rename_i hh; exact absurd (by decide) hh
  right
  have eg : evaluateHOLFiniteState t (.ite (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.const n8)) hang .skip)
      = (none, t) := by
    rw [ite_word t _ _ _ _ hg]; simp only [hfull, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    · rw [evaluateHOLFiniteState_eq_evaluate_def]
  rw [seq_normal _ eg]
  obtain ⟨h', r1, ⟨a1, a2, a3⟩, sub, cells, hp, cd, ck, ma, ta, gl, mm⟩ :=
    tailN_spec t h p0 fs ws hlen hnP hsmall hx hhp hi hfull
  exact ⟨h', r1, ⟨⟨a1, a2, a3⟩, sub, fun j hj => cells j (by omega), hp, cd, ck, ma, ta, gl, mm⟩⟩

end ConPanqueque.Node
