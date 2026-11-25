import ConPanqueque.Logic.Sep
import ConPanqueque.Rep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Rep

/-!
# Tables (memo caches) in Pancake memory

con-leche's kernel memoizes its walks over expression DAGs; in Pancake those
caches are mutable tables: slots `[key, value]` (key `0` empty), a separating
assertion `TableAt`. This file: the representation, its meaning (`find?`), reading
a slot, the lookup loop, proved to compute `find?` (`scanLoop_spec`), and the
insertion loop, proved to compute `insSlots` (`insLoop_spec`), whose lookup
behaviour is `find?_ins`.
-/

namespace ConPanqueque.Table

/-- Slot `i` of a table at `t` with `cap` slots: two words `[key, value]`, key `0`
meaning empty. -/
def slot (t : BitVec 64) (i : Nat) : BitVec 64 := t + BitVec.ofNat 64 (16 * i)

/-- The table's contents as a list of slots `(key, value)`. -/
def TableAt (t : BitVec 64) (slots : List (BitVec 64 × BitVec 64)) : Assn :=
  block t (slots.flatMap fun (k, v) => [.word k, .word v])

/-- What a slot list means: the first slot holding `k` gives its value. -/
def find? (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64) : Option (BitVec 64) :=
  (slots.find? (·.1 = k)).map (·.2)

end ConPanqueque.Table

namespace ConPanqueque.Table

def nT := ofString "t"
def nK := ofString "k"
def nL := ofString "lim"
def nJ := ofString "j"
def nR := ofString "r"
def nG := ofString "go"
def vv (n : MlS) : ExpHOL 64 := .var .local n

/-- One step of the scan: at the end stop; on a matching key record the value and
stop; otherwise move to the next slot. -/
def scanBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv nJ) (vv nL)) (.assign .local nG (.const 0))
    (.ite (.cmp .equal (.load .one (.op .add [vv nT, vv nJ])) (vv nK))
      (.seq (.assign .local nR (.load .one (.op .add [vv nT, vv nJ, .const 8]))) (.assign .local nG (.const 0)))
      (.assign .local nJ (.op .add [vv nJ, .const 16])))

/-- The scan loop. -/
def scanLoop : ProgHOL 64 := .while (vv nG) scanBody

end ConPanqueque.Table

namespace ConPanqueque.Table
open ConPanqueque.Rep

theorem flat_length (slots : List (BitVec 64 × BitVec 64)) :
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v]).length = 2 * slots.length := by
  induction slots with
  | nil => rfl
  | cons p rest ih => obtain ⟨k, v⟩ := p; simp [ih]; omega

theorem flat_get : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (hi : i < slots.length),
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v])[2 * i]? = some (.word (slots[i].1)) ∧
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v])[2 * i + 1]? = some (.word (slots[i].2))
  | [], _, hi => absurd hi (by simp)
  | (k, v) :: rest, 0, _ => by simp
  | (k, v) :: rest, i + 1, hi => by
    have := flat_get rest i (by simpa using hi)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine ⟨?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]
      simpa using this.1
    · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 from by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]
      simpa using this.2

theorem slot_read {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hs : Sat s (TableAt t slots ∗ R))
    (i : Nat) (hi : i < slots.length) :
    (s.memaddrs (t + BitVec.ofNat 64 (16 * i)) ∧ s.memory (t + BitVec.ofNat 64 (16 * i)) = .word slots[i].1) ∧
    (s.memaddrs (t + BitVec.ofNat 64 (16 * i) + 8) ∧ s.memory (t + BitVec.ofNat 64 (16 * i) + 8) = .word slots[i].2) := by
  have hl := flat_length slots
  obtain ⟨g1, g2⟩ := flat_get slots i hi
  have r1 := block_get s _ t R (2 * i) (by rw [hl]; omega) hs
  have r2 := block_get s _ t R (2 * i + 1) (by rw [hl]; omega) hs
  rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans g1)] at r1
  rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans g2)] at r2
  have e1 : BitVec.ofNat 64 (8 * (2 * i)) = BitVec.ofNat 64 (16 * i) := by congr 1; omega
  have e2 : t + BitVec.ofNat 64 (8 * (2 * i + 1)) = t + BitVec.ofNat 64 (16 * i) + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e1] at r1; rw [e2] at r2
  exact ⟨r1, r2⟩

end ConPanqueque.Table

namespace ConPanqueque.Table

theorem find?_at : ∀ (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64) (i : Nat) (hi : i < slots.length),
    (∀ m (hm : m < i), (slots[m]'(by omega)).1 ≠ k) → slots[i].1 = k → find? slots k = some slots[i].2
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | p :: rest, k, 0, _, _, hk => by
    simp only [List.getElem_cons_zero] at hk ⊢; simp [find?, List.find?, hk]
  | p :: rest, k, i + 1, hi, hb, hk => by
    have h0 := hb 0 (by omega)
    simp at h0
    have := find?_at rest k i (by simpa using hi)
      (fun m hm => by have := hb (m + 1) (by omega); rw [List.getElem_cons_succ] at this; exact this)
      (by rw [List.getElem_cons_succ] at hk; exact hk)
    rw [List.getElem_cons_succ]
    simpa [find?, List.find?, h0] using this

theorem find?_none : ∀ (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64),
    (∀ m (hm : m < slots.length), slots[m].1 ≠ k) → find? slots k = none
  | [], _, _ => rfl
  | p :: rest, k, hb => by
    have h0 := hb 0 (by simp)
    simp at h0
    have := find?_none rest k (fun m hm => by
      have := hb (m + 1) (by simp; omega); rw [List.getElem_cons_succ] at this; exact this)
    simpa [find?, List.find?, h0] using this

theorem dJ : nJ ≠ nT ∧ nJ ≠ nK ∧ nJ ≠ nL ∧ nJ ≠ nR ∧ nJ ≠ nG := by decide
theorem dG : nG ≠ nT ∧ nG ≠ nK ∧ nG ≠ nL ∧ nG ≠ nR ∧ nG ≠ nJ := by decide
theorem dR : nR ≠ nT ∧ nR ≠ nK ∧ nR ≠ nL ∧ nR ≠ nJ ∧ nR ≠ nG := by decide

/-- One step of the scan, in its three cases. -/
theorem scanBody_step {σ : Type} (u : PanSemStateFiniteExact 64 σ) (t k : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hn : 16 * slots.length < 2 ^ 64)
    (hi : i ≤ slots.length) (hs : Sat u (TableAt t slots ∗ R))
    (lt : u.locals.lookup nT = some (.val (.word t))) (lk : u.locals.lookup nK = some (.val (.word k)))
    (ll : u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))))
    (lr : ∃ r0, u.locals.lookup nR = some (.val (.word r0)))
    (lg : u.locals.lookup nG = some (.val (.word 1))) :
    (i = slots.length → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) u)) ∧
    (∀ (h : i < slots.length), slots[i].1 = k → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nR (.val (.word slots[i].2)) u))) ∧
    (∀ (h : i < slots.length), slots[i].1 ≠ k → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u)) := by
  obtain ⟨r0, lr⟩ := lr
  have hend : (BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * slots.length)) ↔ i = slots.length := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  refine ⟨fun he => ?_, fun h hk => ?_, fun h hk => ?_⟩
  · unfold scanBody
    rw [ite_word u _ _ _ 1 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he])]
    rw [ite_eq_left (by decide : (1 : BitVec 64) ≠ 0)]
    exact assign_ok u .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, ⟨dv, mv⟩⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold scanBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 1 (by
      simp [evalHOLExact, evalListHOLExact, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk])]
    rw [ite_eq_left (by decide : (1 : BitVec 64) ≠ 0)]
    let u1 := setKvarHOLFinite .local nR (.val (.word slots[i].2)) u
    have e1 : evaluateHOLFiniteState u (.assign .local nR (.load .one (.op .add [vv nT, vv nJ, .const 8]))) =
        (none, u1) := by
      apply assign_ok
      · rw [eval_load_word u _ (t + BitVec.ofNat 64 (16 * i) + 8) (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj,
          wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_assoc]) dv, mv]
      · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lr, shapeOfHOLExact, shapeEqHOL]
    rw [seq_normal _ e1]
    exact assign_ok u1 .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u1, setKvarHOLFinite, setVarHOLFinite, FUPDATE, dR.2.2.2.2,
        lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, _⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold scanBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 0 (by
      simp [evalHOLExact, evalListHOLExact, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, vv, lj, wordOpHOL, wordOp, valueIsWord, valueWord]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lj, shapeOfHOLExact, shapeEqHOL]

/-- `u` agrees with `s` on code, globals and every local outside `xs`. -/
def Frame {σ : Type} (s u : PanSemStateFiniteExact 64 σ) (xs : List MlS) : Prop :=
  u.code = s.code ∧ u.globals = s.globals ∧ ∀ x, x ∉ xs → u.locals.lookup x = s.locals.lookup x

theorem frame_refl {σ : Type} (s : PanSemStateFiniteExact 64 σ) (xs : List MlS) : Frame s s xs :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem frame_set {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS} {x : MlS} (v : ValueHOL 64)
    (hf : Frame s u xs) (hx : x ∈ xs) : Frame s (setKvarHOLFinite .local x v u) xs := by
  obtain ⟨a, b, c⟩ := hf
  refine ⟨by simp [setKvarHOLFinite, setVarHOLFinite, a], by simp [setKvarHOLFinite, setVarHOLFinite, b], fun y hy => ?_⟩
  have : y ≠ x := fun e => hy (e ▸ hx)
  simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ this]; exact c y hy

theorem frame_dec {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS}
    (hf : Frame s u xs) : Frame s (decClockHOLFinite u) xs := by
  obtain ⟨a, b, c⟩ := hf
  exact ⟨by simp [decClockHOLFinite, a], by simp [decClockHOLFinite, b], fun y hy => by simpa [decClockHOLFinite] using c y hy⟩

theorem frame_mem {σ : Type} {s u : PanSemStateFiniteExact 64 σ} {xs : List MlS} (m : BitVec 64 → HolWordLab 64)
    (hf : Frame s u xs) : Frame s { u with memory := m } xs := by
  obtain ⟨a, b, c⟩ := hf
  exact ⟨a, b, c⟩

/-- A local's word value (`0` if absent). -/
def wv {σ : Type} (u : PanSemStateFiniteExact 64 σ) (n : MlS) : BitVec 64 :=
  match u.locals.lookup n with
  | some (.val (.word w)) => w
  | _ => 0

theorem sat_of_eq {σ : Type} {u v : PanSemStateFiniteExact 64 σ} {P : Assn}
    (hm : v.memory = u.memory) (hd : v.memaddrs = u.memaddrs) (hs : Sat u P) : Sat v P := by
  obtain ⟨h, hp, hh⟩ := hs; exact ⟨h, hp, fun a w ha => by rw [hm, hd]; exact hh a w ha⟩

/-- The lookup loop returns `find? slots k` (or `0`), memory unchanged. -/
theorem scanLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hn : 16 * slots.length < 2 ^ 64)
    (hs : Sat s (TableAt t slots ∗ R))
    (lt : s.locals.lookup nT = some (.val (.word t))) (lk : s.locals.lookup nK = some (.val (.word k)))
    (ll : s.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : s.locals.lookup nJ = some (.val (.word 0)))
    (lr : s.locals.lookup nR = some (.val (.word 0)))
    (lg : s.locals.lookup nG = some (.val (.word 1)))
    (hclk : slots.length + 1 ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s scanLoop = (none, s') ∧
      s'.locals.lookup nR = some (.val (.word ((find? slots k).getD 0))) ∧ s'.memory = s.memory ∧
      s'.memaddrs = s.memaddrs ∧ Frame s s' [nJ, nR, nG] ∧ s'.locals.lookup nG = some (.val (.word 0)) ∧ ∃ i, i ≤ slots.length ∧ s'.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
        ((find? slots k).isNone ↔ i = slots.length) ∧ s.clock ≤ s'.clock + (slots.length + 1) := by
  let n := slots.length
  let I : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memory = s.memory ∧ u.memaddrs = s.memaddrs ∧ Frame s u [nJ, nR, nG] ∧
    u.locals.lookup nT = some (.val (.word t)) ∧ u.locals.lookup nK = some (.val (.word k)) ∧
    u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
    ∃ i, i ≤ n ∧ u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
      ((u.locals.lookup nG = some (.val (.word 1)) ∧ u.locals.lookup nR = some (.val (.word 0)) ∧
          (∀ m (hm : m < n), m < i → slots[m].1 ≠ k) ∧ n + 1 - i ≤ u.clock ∧ s.clock ≤ u.clock + i) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧
          u.locals.lookup nR = some (.val (.word ((find? slots k).getD 0))) ∧
          ((find? slots k).isNone ↔ i = n) ∧ s.clock ≤ u.clock + (i + 1)))
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.locals.lookup nR = some (.val (.word ((find? slots k).getD 0))) ∧ u.memory = s.memory ∧
    u.memaddrs = s.memaddrs ∧ Frame s u [nJ, nR, nG] ∧ u.locals.lookup nG = some (.val (.word 0)) ∧
    ∃ i, i ≤ n ∧ u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
      ((find? slots k).isNone ↔ i = n) ∧ s.clock ≤ u.clock + (n + 1)
  let m : PanSemStateFiniteExact 64 σ → Nat := fun u =>
    if wv u nG = 1 then n + 1 - (wv u nJ).toNat / 16 else 0
  have hI0 : I s := ⟨rfl, rfl, frame_refl s _, lt, lk, ll, 0, Nat.zero_le _, by simpa using lj,
    .inl ⟨lg, lr, fun m _ hm => absurd hm (by omega), by omega, by omega⟩⟩
  refine while_rule (vv nG) scanBody I m Q ?_ s hI0
  rintro u ⟨hm, hd, hF, ut, uk, ul, i, hi, uj, hcase⟩
  have hsu : Sat u (TableAt t slots ∗ R) := sat_of_eq hm hd hs
  have wj : (wv u nJ).toNat / 16 = i := by
    simp [wv, uj]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  rcases hcase with ⟨ug, ur, hnot, uclk, ucon⟩ | ⟨ug, ur, hiff, ucon⟩
  · refine ⟨1, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun h => absurd h (by decide), fun _ => ?_⟩
    have g1 : wv u nG = 1 := by simp [wv, ug]
    have mu : m u = n + 1 - i := by simp only [m]; rw [ite_eq_left g1, wj]
    refine ⟨by rw [mu]; exact uclk, by rw [mu]; omega, ?_⟩
    let u0 := decClockHOLFinite u
    have hsu0 : Sat u0 (TableAt t slots ∗ R) := sat_of_eq (by simp [u0, decClockHOLFinite]) (by simp [u0, decClockHOLFinite]) hsu
    obtain ⟨c1, c2, c3⟩ := scanBody_step u0 t k slots R i hn hi hsu0 (by simpa [u0, decClockHOLFinite] using ut)
      (by simpa [u0, decClockHOLFinite] using uk) (by simpa [u0, decClockHOLFinite] using ul)
      (by simpa [u0, decClockHOLFinite] using uj) ⟨0, by simpa [u0, decClockHOLFinite] using ur⟩
      (by simpa [u0, decClockHOLFinite] using ug)
    have uc : u0.clock = u.clock - 1 := by simp [u0, decClockHOLFinite]
    by_cases hin : i = n
    · -- end of the table: not found
      have hres : (find? slots k).getD 0 = 0 := by
        rw [find?_none slots k (fun m hm => hnot m hm (by omega))]; rfl
      refine ⟨_, c1 hin, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
        by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd],
        frame_set _ (frame_dec hF) (by decide), ?_, ?_, ?_, i, hi, ?_,
        .inr ⟨?_, ?_, by rw [find?_none slots k (fun m hm => hnot m hm (by omega))]; simp [hin],
          by simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega⟩⟩, ?_⟩
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1)]; simpa [u0, decClockHOLFinite] using ut
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1)]; simpa [u0, decClockHOLFinite] using uk
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1)]; simpa [u0, decClockHOLFinite] using ul
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2]; simpa [u0, decClockHOLFinite] using uj
      · simp [setKvarHOLFinite]
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.2.1), hres]
        simpa [u0, decClockHOLFinite] using ur
      · have : m (setKvarHOLFinite .local nG (.val (.word 0)) u0) = 0 := by simp [m, wv, setKvarHOLFinite]
        rw [this, mu]; omega
    · have hlt : i < n := by omega
      by_cases hk : slots[i].1 = k
      · -- found at slot i
        have hres : (find? slots k).getD 0 = slots[i].2 := by
          rw [find?_at slots k i hlt (fun m hm => hnot m (by omega) hm) hk]; rfl
        refine ⟨_, c2 hlt hk, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
          by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd],
          frame_set _ (frame_set _ (frame_dec hF) (by decide)) (by decide), ?_, ?_, ?_, i, hi, ?_,
          .inr ⟨?_, ?_, by rw [find?_at slots k i hlt (fun m hm => hnot m (by omega) hm) hk]; simp; omega,
            by simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1), lookup_setVar_other _ _ (Ne.symm dR.1)]
          simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1), lookup_setVar_other _ _ (Ne.symm dR.2.1)]
          simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1), lookup_setVar_other _ _ (Ne.symm dR.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2, lookup_setVar_other _ _ dJ.2.2.2.1]
          simpa [u0, decClockHOLFinite] using uj
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.2.1), hres]; simp
        · have : m (setKvarHOLFinite .local nG (.val (.word 0))
              (setKvarHOLFinite .local nR (.val (.word slots[i].2)) u0)) = 0 := by simp [m, wv, setKvarHOLFinite]
          rw [this, mu]; omega
      · -- move to the next slot
        refine ⟨_, c3 hlt hk, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
          by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd],
          frame_set _ (frame_dec hF) (by decide), ?_, ?_, ?_, i + 1, by omega, ?_,
          .inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.1)]; simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.1)]; simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]; simpa [u0, decClockHOLFinite] using ug
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dR.2.2.2.1]; simpa [u0, decClockHOLFinite] using ur
        · intro m' hm' hmi
          by_cases e : m' = i
          · subst e; exact hk
          · exact hnot m' hm' (by omega)
        · simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega
        · simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega
        · have wj' : (wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nJ).toNat / 16
              = i + 1 := by
            simp [wv, setKvarHOLFinite]; rw [Nat.mod_eq_of_lt (by omega)]; omega
          have g1' : wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nG = 1 := by
            simp only [wv, setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]
            simp [u0, decClockHOLFinite, ug]
          have : m (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) = n + 1 - (i + 1) := by
            simp only [m]; rw [ite_eq_left g1', wj']
          rw [this, mu]; omega
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨ur, hm, hd, hF, ug, i, hi, uj, hiff, by omega⟩,
      fun h => absurd rfl h⟩

/-! ## Insertion: meaning -/

/-- Insert `(k, v)` into the first slot holding `k` or empty (key `0`); `none` if full. -/
def insSlots (k v : BitVec 64) : List (BitVec 64 × BitVec 64) → Option (List (BitVec 64 × BitVec 64))
  | [] => none
  | (k', v') :: rest =>
    if k' = k ∨ k' = 0 then some ((k, v) :: rest)
    else (insSlots k v rest).map ((k', v') :: ·)

theorem find?_ins (k v : BitVec 64) (hk : k ≠ 0) :
    ∀ (slots slots' : List (BitVec 64 × BitVec 64)), insSlots k v slots = some slots' →
      find? slots' k = some v ∧ ∀ k', k' ≠ k → k' ≠ 0 → find? slots' k' = find? slots k'
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, slots', h => by
    simp only [insSlots] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨by simp [find?, List.find?], fun k' hk' hk0 => ?_⟩
      rcases hc with rfl | rfl
      · simp [find?, List.find?, Ne.symm hk', hk']
      · simp [find?, List.find?, Ne.symm hk', show ¬ (0#64 = k') from fun e => hk0 e.symm]
    · rename_i hc
      simp only [not_or] at hc
      cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r =>
        simp [e] at h; subst h
        obtain ⟨h1, h2⟩ := find?_ins k v hk rest r e
        refine ⟨by simpa [find?, List.find?, hc.1] using h1, fun k' hk' hk0 => ?_⟩
        by_cases e1 : k1 = k'
        · subst e1; simp [find?, List.find?]
        · simpa [find?, List.find?, e1] using h2 k' hk' hk0

theorem insSlots_at (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (hi : i < slots.length),
    (∀ m (hm : m < slots.length), m < i → slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) →
    (slots[i].1 = k ∨ slots[i].1 = 0) → insSlots k v slots = some (slots.set i (k, v))
  | [], _, hi, _, _ => absurd hi (by simp)
  | (k1, v1) :: rest, 0, _, _, hc => by simp at hc; simp [insSlots, hc]
  | (k1, v1) :: rest, i + 1, hi, hb, hc => by
    have h0 := hb 0 (by simp) (by omega)
    simp at h0
    have := insSlots_at k v rest i (by simpa using hi)
      (fun m hm hmi => by have := hb (m + 1) (by simp; omega) (by omega); simpa using this)
      (by simpa using hc)
    simp [insSlots, h0, this]

theorem insSlots_none (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)),
    (∀ m (hm : m < slots.length), slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) → insSlots k v slots = none
  | [], _ => rfl
  | (k1, v1) :: rest, hb => by
    have h0 := hb 0 (by simp)
    simp at h0
    have := insSlots_none k v rest (fun m hm => by have := hb (m + 1) (by simp; omega); simpa using this)
    simp [insSlots, h0, this]

theorem flat_set : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (k v : BitVec 64),
    ((slots.set i (k, v)).flatMap fun (k, v) => [HolWordLab.word k, .word v]) =
      (((slots.flatMap fun (k, v) => [HolWordLab.word k, .word v]).set (2 * i) (.word k)).set (2 * i + 1) (.word v))
  | [], _, _, _ => by simp
  | (k1, v1) :: rest, 0, k, v => by simp
  | (k1, v1) :: rest, i + 1, k, v => by
    have := flat_set rest i k v
    simp only [List.set_cons_succ, List.flatMap_cons, List.cons_append, List.nil_append, this]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega, show 2 * i + 1 + 1 + 1 = (2 * i + 1) + 1 + 1 from rfl]
    simp [List.set_cons_succ]

/-! ## Insertion: the loop -/

def nV := ofString "v"
def nO := ofString "ok"

def keyAt : ExpHOL 64 := .load .one (.op .add [vv nT, vv nJ])

/-- One step of insertion: at the end stop (`ok` stays 0); on a slot holding `k` or
empty write `[k, v]`, set `ok`, stop; otherwise move on. -/
def insBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv nJ) (vv nL)) (.assign .local nG (.const 0))
    (.ite (.op .or [.cmp .equal keyAt (vv nK), .cmp .equal keyAt (.const 0)])
      (.seq (.store (.op .add [vv nT, vv nJ]) (vv nK))
        (.seq (.store (.op .add [vv nT, vv nJ, .const 8]) (vv nV))
          (.seq (.assign .local nO (.const 1)) (.assign .local nG (.const 0)))))
      (.assign .local nJ (.op .add [vv nJ, .const 16])))

def insLoop : ProgHOL 64 := .while (vv nG) insBody

/-- Writing slot `i`: two block stores. -/
theorem table_write {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hi : i < slots.length)
    (hs : Sat s (TableAt t slots ∗ R)) :
    let s1 := { s with memory := fun c => if c = t + BitVec.ofNat 64 (16 * i) then .word k else s.memory c }
    let s2 := { s1 with memory := fun c => if c = t + BitVec.ofNat 64 (16 * i) + 8 then .word v else s1.memory c }
    Sat s2 (TableAt t (slots.set i (k, v)) ∗ R) := by
  intro s1 s2
  have hl := flat_length slots
  have a1 := block_set _ t R (2 * i) (by rw [hl]; omega) s (.word k) hs
  have e1 : t + BitVec.ofNat 64 (8 * (2 * i)) = t + BitVec.ofNat 64 (16 * i) := by congr 1; congr 1; omega
  rw [e1] at a1
  have a2 := block_set _ t R (2 * i + 1) (by rw [List.length_set, hl]; omega) s1 (.word v) a1
  have e2 : t + BitVec.ofNat 64 (8 * (2 * i + 1)) = t + BitVec.ofNat 64 (16 * i) + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e2] at a2
  unfold TableAt; rw [flat_set]; exact a2

theorem dO : nO ≠ nT ∧ nO ≠ nK ∧ nO ≠ nL ∧ nO ≠ nJ ∧ nO ≠ nG ∧ nO ≠ nV := by decide
theorem dG' : nG ≠ nV ∧ nG ≠ nO := by decide
theorem dJ' : nJ ≠ nV ∧ nJ ≠ nO := by decide

theorem insBody_step {σ : Type} (u : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hn : 16 * slots.length < 2 ^ 64)
    (hi : i ≤ slots.length) (hs : Sat u (TableAt t slots ∗ R))
    (lt : u.locals.lookup nT = some (.val (.word t))) (lk : u.locals.lookup nK = some (.val (.word k)))
    (lv : u.locals.lookup nV = some (.val (.word v)))
    (ll : u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))))
    (lo : u.locals.lookup nO = some (.val (.word 0)))
    (lg : u.locals.lookup nG = some (.val (.word 1))) :
    (i = slots.length → evaluateHOLFiniteState u insBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) u)) ∧
    (∀ (h : i < slots.length), (slots[i].1 = k ∨ slots[i].1 = 0) →
      ∃ u2 : PanSemStateFiniteExact 64 σ, Sat u2 (TableAt t (slots.set i (k, v)) ∗ R) ∧ u2.locals = u.locals ∧
        u2.memaddrs = u.memaddrs ∧ u2.clock = u.clock ∧ u2.code = u.code ∧ u2.globals = u.globals ∧
        evaluateHOLFiniteState u insBody =
          (none, setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nO (.val (.word 1)) u2))) ∧
    (∀ (h : i < slots.length), slots[i].1 ≠ k → slots[i].1 ≠ 0 → evaluateHOLFiniteState u insBody =
      (none, setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u)) := by
  have hend : (BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * slots.length)) ↔ i = slots.length := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  refine ⟨fun he => ?_, fun h hk => ?_, fun h hk hk0 => ?_⟩
  · unfold insBody
    rw [ite_word u _ _ _ 1 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he])]
    rw [ite_eq_left (by decide : (1 : BitVec 64) ≠ 0)]
    exact assign_ok u .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, ⟨dv, mv⟩⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    let a0 := t + BitVec.ofNat 64 (16 * i)
    let u1 := { u with memory := fun c => if c = a0 then HolWordLab.word k else u.memory c }
    let u2 := { u1 with memory := fun c => if c = a0 + 8 then HolWordLab.word v else u1.memory c }
    refine ⟨u2, table_write u t k v slots R i h hs, rfl, rfl, rfl, rfl, rfl, ?_⟩
    have cw : OrOp.or (if slots[i].1 = k then (1#64 : BitVec 64) else 0#64)
        (OrOp.or (if slots[i].1 = 0#64 then 1#64 else 0#64) 0#64) ≠ 0 := by
      rcases hk with e | e
      · simp only [e, ite_true]; split <;> decide
      · simp only [e, ite_true]; split <;> decide
    unfold insBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ _ (by
      simp [evalHOLExact, evalListHOLExact, keyAt, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rfl)]
    rw [ite_eq_left cw]
    have e1 : evaluateHOLFiniteState u (.store (.op .add [vv nT, vv nJ]) (vv nK)) = (none, u1) :=
      store_word u _ _ a0 k (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj, wordOpHOL, wordOp, valueIsWord,
        valueWord, a0]) (by simp [evalHOLExact, vv, lk]) dk
    have e2 : evaluateHOLFiniteState u1 (.store (.op .add [vv nT, vv nJ, .const 8]) (vv nV)) = (none, u2) :=
      store_word u1 _ _ (a0 + 8) v (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj, wordOpHOL, wordOp, valueIsWord,
        valueWord, a0, u1, BitVec.add_assoc]) (by simp [evalHOLExact, vv, lv, u1]) (by simpa [u1] using dv)
    let u3 := setKvarHOLFinite .local nO (.val (.word 1)) u2
    have e3 : evaluateHOLFiniteState u2 (.assign .local nO (.const 1)) = (none, u3) :=
      assign_ok u2 .local nO _ _ (by simp [evalHOLExact])
        (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u2, u1, lo, shapeOfHOLExact, shapeEqHOL])
    rw [seq_normal _ e1, seq_normal _ e2, seq_normal _ e3]
    exact assign_ok u3 .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u3, u2, u1, setKvarHOLFinite, setVarHOLFinite, FUPDATE,
        dO.2.2.2.2.1, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, _⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold insBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 0 (by
      simp [evalHOLExact, evalListHOLExact, keyAt, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk, show ¬ slots[i].1 = 0#64 from hk0]
      decide)]
    simp only [ne_eq, not_true_eq_false, ite_false]
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, vv, lj, wordOpHOL, wordOp, valueIsWord, valueWord]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lj, shapeOfHOLExact, shapeEqHOL]

/-- The insertion loop: on success `ok = 1` and memory holds `insSlots k v slots`;
if the table is full, `ok = 0` and memory is unchanged. -/
theorem insLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hn : 16 * slots.length < 2 ^ 64)
    (hs : Sat s (TableAt t slots ∗ R))
    (lt : s.locals.lookup nT = some (.val (.word t))) (lk : s.locals.lookup nK = some (.val (.word k)))
    (lv : s.locals.lookup nV = some (.val (.word v)))
    (ll : s.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : s.locals.lookup nJ = some (.val (.word 0)))
    (lo : s.locals.lookup nO = some (.val (.word 0)))
    (lg : s.locals.lookup nG = some (.val (.word 1)))
    (hclk : slots.length + 1 ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s insLoop = (none, s') ∧ s'.memaddrs = s.memaddrs ∧
      s.clock ≤ s'.clock + (slots.length + 1) ∧ Frame s s' [nJ, nO, nG] ∧
      ((s'.locals.lookup nO = some (.val (.word 1)) ∧
          ∃ sl', insSlots k v slots = some sl' ∧ Sat s' (TableAt t sl' ∗ R)) ∨
       (s'.locals.lookup nO = some (.val (.word 0)) ∧ insSlots k v slots = none ∧ s'.memory = s.memory)) := by
  let n := slots.length
  let I : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memaddrs = s.memaddrs ∧ Frame s u [nJ, nO, nG] ∧
    u.locals.lookup nT = some (.val (.word t)) ∧ u.locals.lookup nK = some (.val (.word k)) ∧
    u.locals.lookup nV = some (.val (.word v)) ∧
    u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
    ∃ i, i ≤ n ∧ u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
      ((u.locals.lookup nG = some (.val (.word 1)) ∧ u.locals.lookup nO = some (.val (.word 0)) ∧
          u.memory = s.memory ∧ (∀ m (hm : m < n), m < i → slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) ∧
          n + 1 - i ≤ u.clock ∧ s.clock ≤ u.clock + i) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧ u.locals.lookup nO = some (.val (.word 0)) ∧
          insSlots k v slots = none ∧ u.memory = s.memory ∧ s.clock ≤ u.clock + (i + 1)) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧ u.locals.lookup nO = some (.val (.word 1)) ∧
          (∃ sl', insSlots k v slots = some sl' ∧ Sat u (TableAt t sl' ∗ R)) ∧ s.clock ≤ u.clock + (i + 1)))
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memaddrs = s.memaddrs ∧ s.clock ≤ u.clock + (n + 1) ∧ Frame s u [nJ, nO, nG] ∧
    ((u.locals.lookup nO = some (.val (.word 1)) ∧ ∃ sl', insSlots k v slots = some sl' ∧ Sat u (TableAt t sl' ∗ R)) ∨
     (u.locals.lookup nO = some (.val (.word 0)) ∧ insSlots k v slots = none ∧ u.memory = s.memory))
  let m : PanSemStateFiniteExact 64 σ → Nat := fun u =>
    if wv u nG = 1 then n + 1 - (wv u nJ).toNat / 16 else 0
  have hI0 : I s := ⟨rfl, frame_refl s _, lt, lk, lv, ll, 0, Nat.zero_le _, by simpa using lj,
    .inl ⟨lg, lo, rfl, fun m _ hm => absurd hm (by omega), by omega, by omega⟩⟩
  have key := while_rule (vv nG) insBody I m Q ?_ s hI0
  · obtain ⟨s', ev, hq1, hq2, hq3, hq4⟩ := key
    exact ⟨s', ev, hq1, hq2, hq3, hq4⟩
  rintro u ⟨hd, hF, ut, uk, uv, ul, i, hi, uj, hcase⟩
  have wj : (wv u nJ).toNat / 16 = i := by
    simp [wv, uj]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  rcases hcase with ⟨ug, uo, hm, hnot, uclk, ucon⟩ | ⟨ug, uo, hnone, hm, ucon⟩ | ⟨ug, uo, ⟨sl', hsl, hsat⟩, ucon⟩
  · refine ⟨1, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun h => absurd h (by decide), fun _ => ?_⟩
    have g1 : wv u nG = 1 := by simp [wv, ug]
    have mu : m u = n + 1 - i := by simp only [m]; rw [ite_eq_left g1, wj]
    refine ⟨by rw [mu]; exact uclk, by rw [mu]; omega, ?_⟩
    let u0 := decClockHOLFinite u
    have hsu0 : Sat u0 (TableAt t slots ∗ R) :=
      sat_of_eq (by simp [u0, decClockHOLFinite, hm]) (by simp [u0, decClockHOLFinite, hd]) hs
    have uc : u0.clock = u.clock - 1 := by simp [u0, decClockHOLFinite]
    obtain ⟨c1, c2, c3⟩ := insBody_step u0 t k v slots R i hn hi hsu0 (by simpa [u0, decClockHOLFinite] using ut)
      (by simpa [u0, decClockHOLFinite] using uk) (by simpa [u0, decClockHOLFinite] using uv)
      (by simpa [u0, decClockHOLFinite] using ul) (by simpa [u0, decClockHOLFinite] using uj)
      (by simpa [u0, decClockHOLFinite] using uo) (by simpa [u0, decClockHOLFinite] using ug)
    by_cases hin : i = n
    · -- full
      have hnone : insSlots k v slots = none := insSlots_none k v slots (fun m' hm' => hnot m' hm' (by omega))
      refine ⟨_, c1 hin, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd],
        frame_set _ (frame_dec hF) (by decide), ?_, ?_, ?_, ?_, i, hi,
        ?_, .inr (.inl ⟨?_, ?_, hnone, by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
          by simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega⟩)⟩, ?_⟩
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1)]; simpa [u0, decClockHOLFinite] using ut
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1)]; simpa [u0, decClockHOLFinite] using uk
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.1)]; simpa [u0, decClockHOLFinite] using uv
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1)]; simpa [u0, decClockHOLFinite] using ul
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2]; simpa [u0, decClockHOLFinite] using uj
      · simp [setKvarHOLFinite]
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.2)]; simpa [u0, decClockHOLFinite] using uo
      · have : m (setKvarHOLFinite .local nG (.val (.word 0)) u0) = 0 := by simp [m, wv, setKvarHOLFinite]
        rw [this, mu]; omega
    · have hlt : i < n := by omega
      by_cases hk : slots[i].1 = k ∨ slots[i].1 = 0
      · -- write slot i
        obtain ⟨u2, hsat2, hl2, hd2, hc2, hcode2, hglob2, ev⟩ := c2 hlt hk
        have hF2 : Frame s u2 [nJ, nO, nG] := by
          obtain ⟨a, b, c⟩ := frame_dec hF
          exact ⟨by rw [hcode2]; exact a, by rw [hglob2]; exact b, fun y hy => by rw [hl2]; exact c y hy⟩
        have hins : insSlots k v slots = some (slots.set i (k, v)) :=
          insSlots_at k v slots i hlt (fun m' hm' hmi => hnot m' hm' hmi) hk
        have lk2 : ∀ x, u2.locals.lookup x = u0.locals.lookup x := by intro x; rw [hl2]
        refine ⟨_, ev, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, hd2, u0, decClockHOLFinite, hd],
          frame_set _ (frame_set _ hF2 (by decide)) (by decide), ?_, ?_, ?_, ?_, i, hi,
          ?_, .inr (.inr ⟨?_, ?_, ⟨_, hins, ?_⟩, by simp [setKvarHOLFinite, setVarHOLFinite, hc2, uc]; omega⟩)⟩, ?_⟩
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.1), lookup_setVar_other _ _ (Ne.symm dO.1), lk2]
          simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.1), lookup_setVar_other _ _ (Ne.symm dO.2.1), lk2]
          simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG'.1), lookup_setVar_other _ _ (Ne.symm dO.2.2.2.2.2), lk2]
          simpa [u0, decClockHOLFinite] using uv
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1), lookup_setVar_other _ _ (Ne.symm dO.2.2.1), lk2]
          simpa [u0, decClockHOLFinite] using ul
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ dJ.2.2.2.2, lookup_setVar_other _ _ dJ'.2, lk2]
          simpa [u0, decClockHOLFinite] using uj
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.2)]; simp
        · exact sat_of_eq (by simp [setKvarHOLFinite, setVarHOLFinite]) (by simp [setKvarHOLFinite, setVarHOLFinite]) hsat2
        · have : m (setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nO (.val (.word 1)) u2)) = 0 := by
            simp [m, wv, setKvarHOLFinite]
          rw [this, mu]; omega
      · -- next slot
        simp only [not_or] at hk
        refine ⟨_, c3 hlt hk.1 hk.2, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd],
          frame_set _ (frame_dec hF) (by decide), ?_, ?_, ?_, ?_,
          i + 1, by omega, ?_, .inl ⟨?_, ?_, by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm], ?_, ?_, ?_⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.1)]; simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.1)]; simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ'.1)]; simpa [u0, decClockHOLFinite] using uv
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]; simpa [u0, decClockHOLFinite] using ug
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dO.2.2.2.1]; simpa [u0, decClockHOLFinite] using uo
        · intro m' hm' hmi
          by_cases e : m' = i
          · subst e; exact hk
          · exact hnot m' hm' (by omega)
        · simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega
        · simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega
        · have wj' : (wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nJ).toNat / 16
              = i + 1 := by
            simp [wv, setKvarHOLFinite]; rw [Nat.mod_eq_of_lt (by omega)]; omega
          have g1' : wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nG = 1 := by
            simp only [wv, setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]
            simp [u0, decClockHOLFinite, ug]
          have : m (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) = n + 1 - (i + 1) := by
            simp only [m]; rw [ite_eq_left g1', wj']
          rw [this, mu]; omega
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨hd, by omega, hF, .inr ⟨uo, hnone, hm⟩⟩,
      fun h => absurd rfl h⟩
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨hd, by omega, hF, .inl ⟨uo, sl', hsl, hsat⟩⟩,
      fun h => absurd rfl h⟩

theorem insSlots_length (k v : BitVec 64) : ∀ (slots sl' : List (BitVec 64 × BitVec 64)),
    insSlots k v slots = some sl' → sl'.length = slots.length
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, sl', h => by
    simp only [insSlots] at h
    split at h
    · cases h; simp
    · cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r => simp [e] at h; subst h; simp [insSlots_length k v rest r e]

theorem find?_mem (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)),
    find? slots k = some v → (k, v) ∈ slots
  | [], h => by simp [find?] at h
  | (k1, v1) :: rest, h => by
    simp only [find?, List.find?] at h
    by_cases e : k1 = k
    · simp [e] at h; subst e; subst h; simp
    · simp [e] at h
      have := find?_mem k v rest (by simpa [find?] using h)
      simp [this]

end ConPanqueque.Table
