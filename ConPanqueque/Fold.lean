import ConPanqueque.LevelFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-!
# Generic recursion blocks

`callKids fn kids rest` declares a result local per child and calls `fn` on each
child pointer (at its offset from local `u`), then runs `rest`. `callKids_spec`,
by induction on the list of children: given each child's result (as a hypothesis
about `fn`'s body on that child) and a specification of `rest` assuming the
result locals, the block returns `rest`'s result with code and memory unchanged
and a summed clock bound. Fold templates over any inductive (levels,
expressions) are built from it.
-/

namespace ConPanqueque.Fold

def nU := ofString "u"
def vU : ExpHOL 64 := .var .local nU

/-- For children at offsets `offs` (results into locals `xs`), declare each local and call
`fn` on the child pointer, then run `rest`. -/
def callKids (fn : MlS) : List (MlS × BitVec 64) → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | (x, off) :: kids, rest =>
    .dec x .one (.const 0)
      (.seq (.call (some (some (.local, x), none)) fn [.load .one (.op .add [vU, .const off])])
        (callKids fn kids rest))

end ConPanqueque.Fold

namespace ConPanqueque.Fold

def Post {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (c : Nat) : Prop :=
  st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock ≤ st.clock + c

/-- A child: its result local, offset, pointer, result, and the calls it costs. -/
structure Kid where
  x : MlS
  off : BitVec 64
  q : BitVec 64
  r : UInt64
  c : Nat

def kidsCost : List Kid → Nat
  | [] => 0
  | k :: ks => 1 + k.c + kidsCost ks

theorem callKids_spec {σ : Type} (fn : MlS) (B : ProgHOL 64) (h : Heap) (p : BitVec 64) :
    ∀ (ks : List Kid) (pre : List (MlS × UInt64)) (rest : ProgHOL 64) (W : UInt64) (cr : Nat)
      (t : PanSemStateFiniteExact 64 σ),
      (ks.map Kid.x).Nodup → nU ∉ ks.map Kid.x → (∀ y ∈ pre, y.1 ∉ ks.map Kid.x) →
      (∀ k ∈ ks, h (p + k.off) = some (.word k.q) ∧
        ∀ t' : PanSemStateFiniteExact 64 σ, t'.code.lookup fn = some ([(nU, .one)], B, .one) → InMem t' h →
          t'.locals.lookup nU = some (.val (.word k.q)) → k.c ≤ t'.clock →
          ∃ st, evaluateHOLFiniteState t' B = (some (.returned (.val (.word k.r.toBitVec))), st) ∧ Post t' st k.c) →
      (∀ t' : PanSemStateFiniteExact 64 σ, t'.code = t.code → t'.memory = t.memory → t'.memaddrs = t.memaddrs →
        t'.locals.lookup nU = some (.val (.word p)) →
        (∀ y ∈ pre, t'.locals.lookup y.1 = some (.val (.word y.2.toBitVec))) →
        (∀ k ∈ ks, t'.locals.lookup k.x = some (.val (.word k.r.toBitVec))) → cr ≤ t'.clock →
        ∃ st, evaluateHOLFiniteState t' rest = (some (.returned (.val (.word W.toBitVec))), st) ∧ Post t' st cr) →
      t.code.lookup fn = some ([(nU, .one)], B, .one) → InMem t h →
      t.locals.lookup nU = some (.val (.word p)) →
      (∀ y ∈ pre, t.locals.lookup y.1 = some (.val (.word y.2.toBitVec))) → kidsCost ks + cr ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (callKids fn (ks.map fun k => (k.x, k.off)) rest) =
        (some (.returned (.val (.word W.toBitVec))), st) ∧ Post t st (kidsCost ks + cr)
  | [], pre, rest, W, cr, t, _, _, _, _, hrest, hc, hm, hu, hpre, hck => by
    simpa [callKids, kidsCost] using hrest t rfl rfl rfl hu hpre (by simp) (by simpa [kidsCost] using hck)
  | k :: ks, pre, rest, W, cr, t, hnd, hnu, hpd, hkids, hrest, hc, hm, hu, hpre, hck => by
    obtain ⟨hk0, hkspec⟩ := hkids k (List.mem_cons_self ..)
    obtain ⟨dq, mq⟩ := hm _ _ hk0
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd hnu
    have hxu : k.x ≠ nU := fun e => hnu.1 e.symm
    simp only [kidsCost] at hck
    obtain ⟨L, hdec⟩ := dec_word' t k.x (.const 0) 0
      (.seq (.call (some (some (.local, k.x), none)) fn [.load .one (.op .add [vU, .const k.off])])
        (callKids fn (ks.map fun k => (k.x, k.off)) rest)) (by simp [evalHOLExact])
    let t1 := setVarHOLFinite k.x (.val (.word 0)) t
    have lu1 : t1.locals.lookup nU = some (.val (.word p)) := by
      simp only [t1]; rw [lookup_setVar_other _ _ (Ne.symm hxu)]; exact hu
    obtain ⟨st, ⟨pc, pm, pd, pclk⟩, hcall⟩ := call1 t1 fn nU k.x B (.load .one (.op .add [vU, .const k.off])) k.q
      k.r.toBitVec
      (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧ t.clock - 1 ≤ st.clock + k.c)
      (by simpa [t1, setVarHOLFinite] using hc)
      (by rw [eval_load_word t1 _ (p + k.off) (by simp [evalHOLExact, evalListHOLExact, vU, lu1, wordOpHOL, wordOp,
        valueIsWord, valueWord]) (by simpa [t1, setVarHOLFinite] using dq)]
          simp only [t1, setVarHOLFinite]; rw [mq])
      (by simp [t1, setVarHOLFinite]; omega)
      ⟨0, by simp [t1]⟩
      (fun callee hcl => by
        obtain ⟨st, ev, a1, a2, a3, a4⟩ := hkspec (callEntryStateHOLFinite t1 callee)
          (by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hc)
          (fun a w ha => by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hm a w ha)
          (by simpa [callEntryStateHOLFinite] using hcl)
          (by simp [callEntryStateHOLFinite, t1, setVarHOLFinite]; omega)
        exact ⟨st, ev, by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a1,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a2,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a3,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a4⟩)
    let t2 := setKvarHOLFinite .local k.x (.val (.word k.r.toBitVec)) { st with locals := t1.locals }
    have t2c : t2.code = t.code := by simp [t2, setKvarHOLFinite, setVarHOLFinite, pc]
    have t2m : t2.memory = t.memory := by simp [t2, setKvarHOLFinite, setVarHOLFinite, pm]
    have t2d : t2.memaddrs = t.memaddrs := by simp [t2, setKvarHOLFinite, setVarHOLFinite, pd]
    have t2k : t2.clock = st.clock := by simp [t2, setKvarHOLFinite, setVarHOLFinite]
    have l2 : ∀ y, y ≠ k.x → t2.locals.lookup y = t.locals.lookup y := by
      intro y hy; simp only [t2, setKvarHOLFinite]; rw [lookup_setVar_other _ _ hy]
      simp only [t1]; rw [lookup_setVar_other _ _ hy]
    obtain ⟨st2, ev2, post2⟩ := callKids_spec fn B h p ks ((k.x, k.r) :: pre) rest W cr t2 hnd.2 hnu.2
      (fun y hy => by
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hnd.1
        · exact fun hm' => hpd y hy (by simp [hm']))
      (fun k' hk' => hkids k' (List.mem_cons_of_mem _ hk'))
      (fun t' c' m' d' u' pre' kids' clk' => hrest t' (c'.trans t2c) (m'.trans t2m) (d'.trans t2d) u'
        (fun y hy => pre' y (List.mem_cons_of_mem _ hy))
        (fun k'' hk'' => by
          simp only [List.mem_cons] at hk''
          rcases hk'' with rfl | hk''
          · exact pre' (k''.x, k''.r) (List.mem_cons_self ..)
          · exact kids' k'' hk'') clk')
      (by simpa [t2c] using hc)
      (fun a w ha => by have := hm a w ha; rw [t2m, t2d]; exact this)
      (by rw [l2 _ (Ne.symm hxu)]; exact hu)
      (fun y hy => by
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp [t2, setKvarHOLFinite]
        · have hne : y.1 ≠ k.x := fun e => hpd y hy (by simp [e])
          rw [l2 _ hne]; exact hpre y hy)
      (by rw [t2k]; simp [t1, setVarHOLFinite] at pclk; omega)
    simp only [List.map_cons, callKids]
    rw [hdec, show setVarHOLFinite k.x (.val (.word 0)) t = t1 from rfl, seq_normal _ hcall,
      show setKvarHOLFinite .local k.x (.val (.word k.r.toBitVec)) { st with locals := t1.locals } = t2 from rfl, ev2]
    obtain ⟨b1, b2, b3, b4⟩ := post2
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [b1, t2c]
    · simp [b2, t2m]
    · simp [b3, t2d]
    · simp only [kidsCost]; rw [t2k] at b4; omega

end ConPanqueque.Fold
