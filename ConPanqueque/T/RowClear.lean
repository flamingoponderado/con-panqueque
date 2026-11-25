import ConPanqueque.T.Memo
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Clearing a table row by row

A table's slot array has `2^14` words; zeroing all of them for every declaration costs far more than the
declaration's own checks.  `rowClear` instead walks the rows: for row `i` it hashes the row's key
(`hashLoop`), probes from the key's home slot to the slot naming row `i` (value `i + 1`), and zeroes that
slot.  Every nonzero slot names a row (`Inv.named`) and a row is named by one slot (`Inv.uniq`), so after the
last row every slot is zero, exactly as after the full sweep.

`rowClear_spec`: stop, or the slots are zero, memory outside the slot array is untouched, and only `cj0`
among the locals changed.
-/

namespace ConPanqueque.T

def lJ0 := ofString "cj0"
def rJ := ofString "rcj"
def rV := ofString "rcv"

def maskE (g : VGeo) : ExpHOL 64 := .const (BitVec.ofNat 64 (g.n - 1))
def slotE (g : VGeo) : ExpHOL 64 := .op .add [.const g.S, .shift .lsl (vv rJ) (.const 3)]
def rowE (g : VGeo) : ExpHOL 64 := .op .add [.const g.R, .shift .lsl (vv lJ0) (.const 4)]

/-- Probe forward from `rcj` to the slot holding `cj0 + 1`. -/
def findSlot (g : VGeo) : ProgHOL 64 :=
  .while (.cmp .notEqual (vv rV) (.op .add [vv lJ0, .const 1]))
    (.seq (.assign .local rJ (.op .and [.op .add [vv rJ, .const 1], maskE g]))
      (.assign .local rV (.load .one (slotE g))))

def rowBody (g : VGeo) : ProgHOL 64 :=
  .seq (.assign .local lWa (.load .one (rowE g)))
  (.seq (.assign .local lWn (.load .one (.op .add [rowE g, .const 8])))
  (.seq (.assign .local lWh (.const 0))
  (.seq (.assign .local lWg (.const 1))
  (.seq hashLoop
  (.seq (.assign .local rJ (.op .and [vv lWh, maskE g]))
  (.seq (.assign .local rV (.load .one (slotE g)))
  (.seq (findSlot g)
  (.seq (.store (slotE g) (.const 0))
    (.assign .local lJ0 (.op .add [vv lJ0, .const 1]))))))))))

def rowLoop (g : VGeo) : ProgHOL 64 :=
  .while (.cmp .lower (vv lJ0) (.load .one (.const g.C))) (rowBody g)

def rowClear (g : VGeo) : ProgHOL 64 :=
  .dec lWa .one (.const 0) (.dec lWn .one (.const 0) (.dec lWh .one (.const 0) (.dec lWg .one (.const 0)
  (.dec rJ .one (.const 0) (.dec rV .one (.const 0)
    (.seq (.assign .local lJ0 (.const 0)) (rowLoop g)))))))

/-- Slot `j` once rows below `i` are cleared. -/
def cur (slots : List Nat) (i j : Nat) : Nat :=
  if slots.getD j 0 ≠ 0 ∧ slots.getD j 0 ≤ i then 0 else slots.getD j 0

def tmpR : List MlS := [lWa, lWn, lWh, lWg, rJ, rV]

theorem cur_eq_succ {slots : List Nat} {i j : Nat} (h : cur slots i j = i + 1) : slots[j]? = some (i + 1) := by
  unfold cur at h
  split at h
  · cases h
  · rename_i hn
    have hv : slots.getD j 0 = i + 1 := h
    by_cases hj : j < slots.length
    · rw [List.getElem?_eq_getElem hj]; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some] at hv; rw [hv]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ j),
        Option.getD_none] at hv; omega

theorem cur_of_succ {slots : List Nat} {i j : Nat} (h : slots[j]? = some (i + 1)) : cur slots i j = i + 1 := by
  have hv : slots.getD j 0 = i + 1 := by simp [List.getD_eq_getElem?_getD, h]
  unfold cur; rw [hv]; simp

theorem cur_step {slots : List Nat} {i j j' : Nat} (hj : slots[j]? = some (i + 1))
    (hu : ∀ x, slots[x]? = some (i + 1) → x = j) (x : Nat) :
    cur slots (i + 1) x = if x = j then 0 else cur slots i x := by
  by_cases e : x = j
  · subst e; have hv : slots.getD x 0 = i + 1 := by simp [List.getD_eq_getElem?_getD, hj]
    unfold cur; rw [hv]; simp
  · rw [if_neg e]; unfold cur
    have hne : slots.getD x 0 ≠ i + 1 := by
      intro hv; apply e; apply hu
      by_cases hx : x < slots.length
      · rw [List.getElem?_eq_getElem hx]; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx,
          Option.getD_some] at hv; rw [hv]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ x),
          Option.getD_none] at hv; omega
    by_cases h1 : slots.getD x 0 ≠ 0 ∧ slots.getD x 0 ≤ i
    · rw [if_pos h1, if_pos (show slots.getD x 0 ≠ 0 ∧ slots.getD x 0 ≤ i + 1 from ⟨h1.1, by omega⟩)]
    · rw [if_neg h1, if_neg (show ¬ (slots.getD x 0 ≠ 0 ∧ slots.getD x 0 ≤ i + 1) from
        fun h2 => h1 ⟨h2.1, by omega⟩)]

theorem cur_done {α : Type} {home : α → Nat} {rows : List α} {slots : List Nat} {n : Nat}
    (hinv : ConsModel.Inv home rows slots n) (j : Nat) : cur slots rows.length j = 0 := by
  unfold cur
  split
  · rfl
  · rename_i h
    by_cases hj : j < slots.length
    · have hv := List.getElem?_eq_getElem hj
      generalize hw : slots[j] = w at hv
      cases w with
      | zero => simp [List.getD_eq_getElem?_getD, hv]
      | succ k =>
        have := hinv.named j k hv
        exact absurd ⟨by simp [List.getD_eq_getElem?_getD, hv], by simp [List.getD_eq_getElem?_getD, hv]; omega⟩ h
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ j)]

theorem cur_lt {slots : List Nat} {i j : Nat} (h : ∀ v, slots[j]? = some v → v < 2 ^ 60) : cur slots i j < 2 ^ 60 := by
  unfold cur
  split
  · exact Nat.two_pow_pos _
  · by_cases hj : j < slots.length
    · have hv := List.getElem?_eq_getElem hj
      simp only [List.getD_eq_getElem?_getD, hv, Option.getD_some]; exact h _ hv
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : slots.length ≤ j)]

theorem at_succ' (n h d : Nat) : (at_ n h d + 1) % n = at_ n h (d + 1) := by
  simp only [at_]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

theorem at_inj {n h d d' : Nat} (hd : d < n) (hd' : d' < n) (e : at_ n h d = at_ n h d') : d = d' := by
  simp only [at_] at e
  have : (h + d) % n = (h + d') % n := e
  rcases Nat.lt_or_ge d d' with c | c
  · have := Nat.sub_mod_eq_zero_of_mod_eq this.symm
    rw [show h + d' - (h + d) = d' - d by omega] at this
    have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero this); omega
  · rcases Nat.lt_or_ge d' d with c' | c'
    · have := Nat.sub_mod_eq_zero_of_mod_eq this
      rw [show h + d - (h + d') = d - d' by omega] at this
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero this); omega
    · omega

section
variable {σ : Type}

theorem ofNat_ne_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp at this; omega
  · intro e; rw [e]

/-- The slot address of slot `j`. -/
theorem eval_slotE (s : PState σ) (g : VGeo) (j : Nat) (hj : j < 2 ^ 60)
    (hJ : s.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 j)))) :
    T.EV s (slotE g) = some (.val (.word (g.S + BitVec.ofNat 64 (8 * j)))) := by
  have e := eval_add2 s (.const g.S) (.shift .lsl (vv rJ) (.const 3)) g.S _ (eval_const s g.S)
    (eval_shl s (vv rJ) 3 _ (eval_vv s rJ _ hJ) (by decide))
  rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)] at e
  exact e

theorem eval_rowE (s : PState σ) (g : VGeo) (i : Nat) (hi : i < 2 ^ 58)
    (hI : s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i)))) :
    T.EV s (rowE g) = some (.val (.word (g.R + BitVec.ofNat 64 (16 * i)))) := by
  have e := eval_add2 s (.const g.R) (.shift .lsl (vv lJ0) (.const 4)) g.R _ (eval_const s g.R)
    (eval_shl s (vv lJ0) 4 _ (eval_vv s lJ0 _ hI) (by decide))
  rw [show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)] at e
  exact e

/-- The row loop's invariant over the base state `b` (the state at the loop's entry, `cj0` aside). -/
def RI (b : PState σ) (g : VGeo) (slots : List Nat) (nr : Nat) (s : PState σ) : Prop :=
  s.memaddrs = b.memaddrs ∧ s.code = b.code ∧ s.globals = b.globals ∧ s.topAddr = b.topAddr ∧
  (∀ y, y ≠ lJ0 → y ∉ tmpR → s.locals.lookup y = b.locals.lookup y) ∧
  (∀ y, y ∈ tmpR → ∃ w, s.locals.lookup y = some (.val (.word w))) ∧
  ∃ i, i ≤ nr ∧ s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) ∧
    (∀ j, j < g.n → s.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 (cur slots i j))) ∧
    (∀ c, (∀ j, j < g.n → c ≠ g.S + BitVec.ofNat 64 (8 * j)) → s.memory c = b.memory c)

/-- The probe's invariant for row `i` (home `h`, its slot `d` steps along) over the state `u` after the probe's
first read. -/
def FI (u : PState σ) (g : VGeo) (slots : List Nat) (i h d : Nat) (s : PState σ) : Prop :=
  s.memory = u.memory ∧ s.memaddrs = u.memaddrs ∧ s.code = u.code ∧ s.globals = u.globals ∧
  s.topAddr = u.topAddr ∧ (∀ y, y ≠ rJ → y ≠ rV → s.locals.lookup y = u.locals.lookup y) ∧
  ∃ d', d' ≤ d ∧ s.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 (at_ g.n h d')))) ∧
    s.locals.lookup rV = some (.val (.word (BitVec.ofNat 64 (cur slots i (at_ g.n h d')))))

theorem findSlot_spec (u : PState σ) (g : VGeo) (slots : List Nat) (i h d : Nat)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hlen : slots.length = g.n) (hd : d < g.n) (hi : i + 1 < 2 ^ 60)
    (hsd : slots[at_ g.n h d]? = some (i + 1))
    (huq : ∀ x, slots[x]? = some (i + 1) → x = at_ g.n h d)
    (hsl : ∀ j, j < g.n → ∀ v, slots[j]? = some v → v < 2 ^ 60)
    (hS : g.S.toNat + 8 * g.n < 2 ^ 64)
    (hmem : ∀ j, j < g.n → u.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧
      u.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 (cur slots i j)))
    (hI : u.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))))
    (hJ : u.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 (at_ g.n h 0)))))
    (hV : u.locals.lookup rV = some (.val (.word (BitVec.ofNat 64 (cur slots i (at_ g.n h 0)))))) :
    Stop (evaluateHOLFiniteState u (findSlot g)).1 ∨ ((evaluateHOLFiniteState u (findSlot g)).1 = none ∧
      FI u g slots i h d (evaluateHOLFiniteState u (findSlot g)).2 ∧
      (evaluateHOLFiniteState u (findSlot g)).2.locals.lookup rJ =
        some (.val (.word (BitVec.ofNat 64 (at_ g.n h d))))) := by
  have hpos : 0 < g.n := by omega
  have hn60 : g.n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hat : ∀ e, at_ g.n h e < g.n := fun e => Nat.mod_lt _ hpos
  have hcur : ∀ j, j < g.n → cur slots i j < 2 ^ 60 := fun j hj => cur_lt (hsl j hj)
  have hJ0 : u.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) := hI
  have hloop := while_stop (.cmp .notEqual (vv rV) (.op .add [vv lJ0, .const 1]))
    (.seq (.assign .local rJ (.op .and [.op .add [vv rJ, .const 1], maskE g]))
      (.assign .local rV (.load .one (slotE g))))
    (FI u g slots i h d)
    (fun s => FI u g slots i h d s ∧ s.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 (at_ g.n h d)))))
    (fun s hs => by
      obtain ⟨hm, had, hc, hg, hta, hfr, d', hd', hj, hv⟩ := hs
      have hi0 : s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) := by
        rw [hfr lJ0 (by decide) (by decide)]; exact hJ0
      have hcmp : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notEqual (vv rV) (.op .add [vv lJ0, .const 1])) =
          some (.val (.word (bw (cur slots i (at_ g.n h d') ≠ i + 1)))) := by
        simp only [evalHOLFinite]
        rw [ConsLoop.eval_cmp_of s .notEqual _ _ _ _ (eval_vv s rV _ hv)
          (eval_add2 s _ _ _ _ (eval_vv s lJ0 _ hi0) (eval_const s 1))]
        have e : (BitVec.ofNat 64 (cur slots i (at_ g.n h d')) = BitVec.ofNat 64 i + 1) ↔
            cur slots i (at_ g.n h d') = i + 1 := by
          rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by
            apply BitVec.eq_of_toNat_eq; simp <;> omega]
          exact ofNat_ne_ofNat (by have := hcur _ (hat d'); omega) (by omega)
        by_cases hc' : cur slots i (at_ g.n h d') = i + 1
        · rw [e.mpr hc']; simp [bw, hc', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        · have : ¬ BitVec.ofNat 64 (cur slots i (at_ g.n h d')) = BitVec.ofNat 64 i + 1 := fun x => hc' (e.mp x)
          simp [bw, hc', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this
      by_cases hc' : cur slots i (at_ g.n h d') = i + 1
      · -- found: `d' = d`
        refine ⟨0, by rw [hcmp]; simp [bw, hc'], fun _ => ⟨⟨hm, had, hc, hg, hta, hfr, d', hd', hj, hv⟩, ?_⟩,
          fun e => absurd rfl e⟩
        rw [hj, at_inj (by omega) hd (huq _ (cur_eq_succ hc'))]
      · have hlt : d' < d := by
          rcases Nat.lt_or_ge d' d with c | c
          · exact c
          · have : d' = d := by omega
            subst this; exact absurd (cur_of_succ hsd) hc'
        refine ⟨1, by rw [hcmp]; simp [bw, hc'], fun e => absurd e (by decide), fun _ _ => ?_⟩
        let s1 := decClockHOLFinite s
        have hj1 : s1.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 (at_ g.n h d')))) := hj
        have hmask : T.EV s1 (.op .and [.op .add [vv rJ, .const 1], maskE g]) =
            some (.val (.word (BitVec.ofNat 64 (at_ g.n h (d' + 1))))) := by
          have e1 := eval_add2 s1 _ _ _ _ (eval_vv s1 rJ _ hj1) (eval_const s1 1)
          rw [show (T.EV s1 (.op .and [.op .add [vv rJ, .const 1], maskE g])) = _ from
            ConPanqueque.V.eval_and2' s1 _ _ _ _ e1 (eval_const s1 (BitVec.ofNat 64 (g.n - 1)))]
          congr 3
          rw [show BitVec.ofNat 64 (at_ g.n h d') + 1 = BitVec.ofNat 64 (at_ g.n h d' + 1) by
            apply BitVec.eq_of_toNat_eq; simp; try (have := hat d'; omega), hn,
            ConsLoop.and_mask _ _ (by omega) (by rw [← hn]; exact hat d'), ← hn, at_succ']
        obtain ⟨wv, hwv⟩ : ∃ w, s1.locals.lookup rJ = some (.val (.word w)) := ⟨_, hj1⟩
        rw [seq_normal _ (ConsLoop.assign_local s1 rJ _ _ _ hmask hwv)]
        let s2 := setVarHOLFinite rJ (.val (.word (BitVec.ofNat 64 (at_ g.n h (d' + 1))))) s1
        have hj2 : s2.locals.lookup rJ = some (.val (.word (BitVec.ofNat 64 (at_ g.n h (d' + 1))))) :=
          lookup_setVar_same _ _ _
        have hA := eval_slotE s2 g _ (by have := hat (d' + 1); omega) hj2
        obtain ⟨hdom, hval⟩ := hmem _ (hat (d' + 1))
        have hdom2 : s2.memaddrs (g.S + BitVec.ofNat 64 (8 * at_ g.n h (d' + 1))) := by
          show s.memaddrs _; rw [had]; exact hdom
        have hld := eval_load_word s2 _ _ hA hdom2
        have hval2 : s2.memory (g.S + BitVec.ofNat 64 (8 * at_ g.n h (d' + 1))) =
            .word (BitVec.ofNat 64 (cur slots i (at_ g.n h (d' + 1)))) := by
          show s.memory _ = _; rw [hm]; exact hval
        rw [hval2] at hld
        have hv2 : s2.locals.lookup rV = some (.val (.word (BitVec.ofNat 64 (cur slots i (at_ g.n h d'))))) := by
          rw [lookup_setVar_other _ _ (by decide)]; exact hv
        rw [ConsLoop.assign_local s2 rV _ _ _ hld hv2]
        refine Or.inr ⟨rfl, hm, had, hc, hg, hta, fun y h1 h2 => ?_, d' + 1, by omega, ?_, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h1]; exact hfr y h1 h2
        · rw [lookup_setVar_other _ _ (by decide)]; exact hj2)
    u ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, 0, Nat.zero_le _, hJ, hV⟩
  rcases hloop with hs | ⟨hn', hq, hj⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn', hq, hj⟩

/-- Addresses of the table: what the row clear needs of `VT`'s layout. -/
theorem slot_toNat (g : VGeo) (hS : g.S.toNat + 8 * g.n < 2 ^ 64) (j : Nat) (hj : j < g.n) :
    (g.S + BitVec.ofNat 64 (8 * j)).toNat = g.S.toNat + 8 * j := toNat_add_of_lt _ _ (by omega)

theorem slot_inj (g : VGeo) (hS : g.S.toNat + 8 * g.n < 2 ^ 64) {j j' : Nat} (hj : j < g.n) (hj' : j' < g.n)
    (e : g.S + BitVec.ofNat 64 (8 * j) = g.S + BitVec.ofNat 64 (8 * j')) : j = j' := by
  have := congrArg BitVec.toNat e; rw [slot_toNat g hS j hj, slot_toNat g hS j' hj'] at this; omega

/-- An address at or above `R` is no slot. -/
theorem not_slot (g : VGeo) (hS : g.S.toNat + 8 * g.n ≤ g.R.toNat) (c : BitVec 64) (hc : g.R.toNat ≤ c.toNat)
    (j : Nat) (hj : j < g.n) : c ≠ g.S + BitVec.ofNat 64 (8 * j) := by
  intro e; have := congrArg BitVec.toNat e
  rw [toNat_add_of_lt _ _ (by have := c.isLt; omega)] at this; omega

theorem rowBody_spec {α : Type} (b : PState σ) (g : VGeo) (enc : α → List (BitVec 64)) (rows : List α)
    (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat)
    (hT : VT b enc rows ders slots g hu) (hinv : ConsModel.Inv (homeV enc g.b) rows slots g.n)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30)
    (s : PState σ) (hs : RI b g slots rows.length s) (i : Nat) (hi : i < rows.length)
    (hI : s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i)))) :
    Stop (evaluateHOLFiniteState s (rowBody g)).1 ∨ ((evaluateHOLFiniteState s (rowBody g)).1 = none ∧
      RI b g slots rows.length (evaluateHOLFiniteState s (rowBody g)).2 ∧
      (evaluateHOLFiniteState s (rowBody g)).2.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 (i + 1))))) := by
  obtain ⟨had, hcd, hgl, hta, hfr, htw, i0, _, hI0, hsl, hout⟩ := hs
  have hii : i = i0 := by
    rw [hI0] at hI; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hI
    have := congrArg BitVec.toNat hI; simp at this
    have := hT.le; omega
  subst hii
  have lC := hT.layC; have lS := hT.layS; have lR := hT.layR; have lD := hT.layD; have lK := hT.layK
  have hle := hT.le
  have hpos : 0 < g.n := hinv.pos
  have hn56 : g.n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hS : g.S.toNat + 8 * g.n < 2 ^ 64 := by omega
  obtain ⟨P, hdR, hdR8, hmR, hmR8, hW, hP1, hP2⟩ := hT.row i hi
  have hshort := hT.short i hi
  have hhu := hT.hu_le
  -- row cells are no slots
  have hR16 : (g.R + BitVec.ofNat 64 (16 * i)).toNat = g.R.toNat + 16 * i := toNat_add_of_lt _ _ (by omega)
  have hR168 : (g.R + BitVec.ofNat 64 (16 * i) + 8).toNat = g.R.toNat + 16 * i + 8 := by
    rw [toNat_add8 _ (by omega), hR16]
  have nsR := not_slot g lS (g.R + BitVec.ofNat 64 (16 * i)) (by omega)
  have nsR8 := not_slot g lS (g.R + BitVec.ofNat 64 (16 * i) + 8) (by omega)
  have twa := htw lWa (by decide); have twn := htw lWn (by decide); have twh := htw lWh (by decide)
  have twg := htw lWg (by decide); have twj := htw rJ (by decide); have twv := htw rV (by decide)
  obtain ⟨wa, hwa⟩ := twa; obtain ⟨wn, hwn⟩ := twn; obtain ⟨wh, hwh⟩ := twh; obtain ⟨wg, hwg⟩ := twg
  obtain ⟨wj, hwj⟩ := twj; obtain ⟨wv, hwv⟩ := twv
  unfold rowBody
  -- 1. cwa := row pointer
  have e1 : T.EV s (.load .one (rowE g)) = some (.val (.word P)) := by
    have := eval_load_word s _ _ (eval_rowE s g i (by omega) hI0) (by rw [had]; exact hdR)
    rw [hout _ (fun j hj => nsR j hj), hmR] at this; exact this
  rw [seq_normal _ (ConsLoop.assign_local s lWa _ _ _ e1 hwa)]
  let s1 := setVarHOLFinite lWa (.val (.word P)) s
  have hI1 : s1.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) := by
    rw [lookup_setVar_other _ _ (by decide)]; exact hI0
  -- 2. cwn := row length
  have e2 : T.EV s1 (.load .one (.op .add [rowE g, .const 8])) =
      some (.val (.word (BitVec.ofNat 64 (enc rows[i]).length))) := by
    have := eval_load_word s1 _ _ (eval_add2 s1 _ _ _ _ (eval_rowE s1 g i (by omega) hI1) (eval_const s1 8))
      (by show s.memaddrs _; rw [had]; exact hdR8)
    have hm8 : s1.memory (g.R + BitVec.ofNat 64 (16 * i) + 8) = .word (BitVec.ofNat 64 (enc rows[i]).length) := by
      show s.memory _ = _; rw [hout _ (fun j hj => nsR8 j hj), hmR8]
    rw [hm8] at this; exact this
  rw [seq_normal _ (ConsLoop.assign_local s1 lWn _ _ wn e2 (by rw [lookup_setVar_other _ _ (by decide)]; exact hwn))]
  let s2 := setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 (enc rows[i]).length))) s1
  rw [seq_normal _ (ConsLoop.assign_local s2 lWh (.const 0) 0 wh (eval_const s2 0)
    (by rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact hwh))]
  let s3 := setVarHOLFinite lWh (.val (.word 0)) s2
  rw [seq_normal _ (ConsLoop.assign_local s3 lWg (.const 1) 1 wg (eval_const s3 1)
    (by rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
      lookup_setVar_other _ _ (by decide)]; exact hwg))]
  let s4 := setVarHOLFinite lWg (.val (.word 1)) s3
  -- 3. hash the key
  have hW4 : Words s4 P (enc rows[i]) := by
    intro k hk
    obtain ⟨a1, a2⟩ := hW k hk
    have hPk : (P + BitVec.ofNat 64 (8 * k)).toNat = P.toNat + 8 * k := toNat_add_of_lt _ _ (by omega)
    refine ⟨by show s.memaddrs _; rw [had]; exact a1, ?_⟩
    show s.memory _ = _
    rw [hout _ (fun j hj => not_slot g lS _ (by omega) j hj)]; exact a2
  rcases hashLoop_spec s4 P (enc rows[i]) (by omega) hW4
      (by lk [s4, s3, s2, s1]) (by lk [s4, s3, s2]) (by lk [s4, s3])
      (lookup_setVar_same _ _ _) with hst | ⟨hn5, hHI, hh5⟩
  · exact Or.inl (seq_stop _ _ _ hst)
  have e5 : evaluateHOLFiniteState s4 hashLoop = (none, (evaluateHOLFiniteState s4 hashLoop).2) := by rw [← hn5]
  rw [seq_normal _ e5]
  generalize (evaluateHOLFiniteState s4 hashLoop).2 = s5 at hHI hh5
  obtain ⟨hm5, hd5, hc5, hg5, ht5, hfr5, k5, -, hwa5, hwn5, hbr5⟩ := hHI
  have hwg5 : ∃ w, s5.locals.lookup lWg = some (.val (.word w)) := by
    rcases hbr5 with ⟨x, -⟩ | ⟨x, -⟩ <;> exact ⟨_, x⟩
  have lk5 : ∀ y, y ≠ lWa → y ≠ lWn → y ≠ lWh → y ≠ lWg → s5.locals.lookup y = s.locals.lookup y := by
    intro y h1 h2 h3 h4
    rw [hfr5 y h1 h2 h3 h4]; simp only [s4, s3, s2, s1]
    rw [lookup_setVar_other _ _ h4, lookup_setVar_other _ _ h3, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h1]
  -- 4. cj := home
  let h := homeV enc g.b rows[i]
  have hh : h < g.n := hinv.home_lt _
  have hat0 : at_ g.n h 0 = h := by simp [at_, Nat.mod_eq_of_lt hh]
  have e6 : T.EV s5 (.op .and [vv lWh, maskE g]) = some (.val (.word (BitVec.ofNat 64 (at_ g.n h 0)))) := by
    have := ConPanqueque.V.eval_and2' s5 _ _ _ _ (eval_vv s5 lWh _ hh5) (eval_const s5 (BitVec.ofNat 64 (g.n - 1)))
    have hv : hashW (enc rows[i]) &&& BitVec.ofNat 64 (g.n - 1) = BitVec.ofNat 64 (at_ g.n h 0) := by
      rw [hat0, hn, ConsIntern.home_mask _ _ hb]; rfl
    rw [hv] at this; exact this
  rw [seq_normal _ (ConsLoop.assign_local s5 rJ _ _ wj e6
    (by rw [lk5 rJ (by decide) (by decide) (by decide) (by decide)]; exact hwj))]
  let s6 := setVarHOLFinite rJ (.val (.word (BitVec.ofNat 64 (at_ g.n h 0)))) s5
  -- 5. cv := slot
  have hmem6 : ∀ j, j < g.n → s6.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧
      s6.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 (cur slots i j)) := by
    intro j hj
    obtain ⟨v, _, _, a3, _⟩ := hT.slot j hj
    refine ⟨by show s5.memaddrs _; rw [hd5]; show s.memaddrs _; rw [had]; exact a3, ?_⟩
    show s5.memory _ = _; rw [hm5]; exact hsl j hj
  have hat0n : at_ g.n h 0 < g.n := Nat.mod_lt _ hpos
  have e7 : T.EV s6 (.load .one (slotE g)) = some (.val (.word (BitVec.ofNat 64 (cur slots i (at_ g.n h 0))))) := by
    have := eval_load_word s6 _ _ (eval_slotE s6 g _ (by omega) (lookup_setVar_same _ _ _)) (hmem6 _ hat0n).1
    rw [(hmem6 _ hat0n).2] at this; exact this
  rw [seq_normal _ (ConsLoop.assign_local s6 rV _ _ wv e7
    (by rw [lookup_setVar_other _ _ (by decide), lk5 rV (by decide) (by decide) (by decide) (by decide)]; exact hwv))]
  let s7 := setVarHOLFinite rV (.val (.word (BitVec.ofNat 64 (cur slots i (at_ g.n h 0))))) s6
  -- 6. probe to the row's slot
  obtain ⟨d, hd, hsd, -⟩ := hinv.reach i hi
  have hslot : ∀ j, j < g.n → ∀ v, slots[j]? = some v → v < 2 ^ 60 := by
    intro j hj v hv
    obtain ⟨v', hv', hlt, -⟩ := hT.slot j hj
    rw [hv] at hv'; cases hv'; exact hlt
  have hI6 : s7.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) := by
    simp only [s7, s6]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide),
      lk5 lJ0 (by decide) (by decide) (by decide) (by decide)]; exact hI0
  rcases findSlot_spec s7 g slots i h d hn hb hinv.len hd (by omega) hsd
      (fun x hx => hinv.uniq x _ i hx hsd)
      hslot hS hmem6 hI6
      (by lk [s7, s6])
      (lookup_setVar_same _ _ _) with hst | ⟨hn8, hFI, hj8⟩
  · exact Or.inl (seq_stop _ _ _ hst)
  have e8 : evaluateHOLFiniteState s7 (findSlot g) = (none, (evaluateHOLFiniteState s7 (findSlot g)).2) := by
    rw [← hn8]
  rw [seq_normal _ e8]
  generalize (evaluateHOLFiniteState s7 (findSlot g)).2 = s8 at hFI hj8
  obtain ⟨hm8, hd8, hc8, hg8, ht8, hfr8, d8, -, -, hv8⟩ := hFI
  -- 7. zero the slot
  let jd := at_ g.n h d
  have hjd : jd < g.n := Nat.mod_lt _ hpos
  have hA8 := eval_slotE s8 g jd (by omega) hj8
  have hdom8 : s8.memaddrs (g.S + BitVec.ofNat 64 (8 * jd)) := by
    rw [hd8]; exact (hmem6 jd hjd).1
  rw [seq_normal _ (store_word s8 _ _ _ 0 hA8 (eval_const s8 0) hdom8)]
  let s9 : PState σ := { s8 with memory := fun c => if c = g.S + BitVec.ofNat 64 (8 * jd) then .word 0 else s8.memory c }
  have hI9 : s9.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 i))) := by
    show s8.locals.lookup lJ0 = _; rw [hfr8 lJ0 (by decide) (by decide)]; exact hI6
  have e10 : T.EV s9 (.op .add [vv lJ0, .const 1]) = some (.val (.word (BitVec.ofNat 64 (i + 1)))) := by
    have := eval_add2 s9 _ _ _ _ (eval_vv s9 lJ0 _ hI9) (eval_const s9 1)
    rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by
      apply BitVec.eq_of_toNat_eq; simp; try omega] at this
    exact this
  rw [ConsLoop.assign_local s9 lJ0 _ _ _ e10 hI9]
  -- the new invariant
  have lk8 : ∀ y, y ≠ lJ0 → y ∉ tmpR → s8.locals.lookup y = s.locals.lookup y := by
    intro y h0 hy
    simp only [tmpR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨y1, y2, y3, y4, y5, y6⟩ := hy
    rw [hfr8 y y5 y6]; simp only [s7, s6]
    rw [lookup_setVar_other _ _ y6, lookup_setVar_other _ _ y5]; exact lk5 y y1 y2 y3 y4
  have hmem8 : ∀ c, s8.memory c = s.memory c := by
    intro c; rw [hm8]; show s5.memory c = _; rw [hm5]; rfl
  refine Or.inr ⟨rfl, ⟨?_, ?_, ?_, ?_, fun y h0 hy => ?_, fun y hy => ?_, i + 1, by omega,
    lookup_setVar_same _ _ _, fun j hj => ?_, fun c hc => ?_⟩, lookup_setVar_same _ _ _⟩
  · show s8.memaddrs = _; rw [hd8]; show s5.memaddrs = _; rw [hd5]; exact had
  · show s8.code = _; rw [hc8]; show s5.code = _; rw [hc5]; exact hcd
  · show s8.globals = _; rw [hg8]; show s5.globals = _; rw [hg5]; exact hgl
  · show s8.topAddr = _; rw [ht8]; show s5.topAddr = _; rw [ht5]; exact hta
  · rw [lookup_setVar_other _ _ h0]; show s8.locals.lookup y = _; rw [lk8 y h0 hy]; exact hfr y h0 hy
  · by_cases e : y = lJ0
    · subst e; exact absurd hy (by decide)
    rw [lookup_setVar_other _ _ e]
    show ∃ w, s8.locals.lookup y = _
    by_cases ej : y = rJ
    · subst ej; exact ⟨_, hj8⟩
    by_cases ev : y = rV
    · subst ev; exact ⟨_, hv8⟩
    rw [hfr8 y ej ev]; simp only [s7, s6]
    rw [lookup_setVar_other _ _ ev, lookup_setVar_other _ _ ej]
    simp only [tmpR, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, hwa5⟩
    · exact ⟨_, hwn5⟩
    · exact ⟨_, hh5⟩
    · exact hwg5
    · exact absurd rfl ej
    · exact absurd rfl ev
  · show (if _ then _ else _) = _
    have hcs := cur_step (j' := 0) hsd (fun x hx => hinv.uniq x _ i hx hsd) j
    split
    · rename_i e
      have := slot_inj g hS hj hjd e
      rw [hcs, if_pos this]; rfl
    · rename_i e
      have hne : j ≠ jd := fun x => e (by rw [x])
      rw [hcs, if_neg hne, hmem8]; exact hsl j hj
  · show (if _ then _ else _) = _
    rw [if_neg (hc jd hjd), hmem8]; exact hout c hc

theorem rowLoop_spec {α : Type} (b : PState σ) (g : VGeo) (enc : α → List (BitVec 64)) (rows : List α)
    (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat)
    (hT : VT b enc rows ders slots g hu) (hinv : ConsModel.Inv (homeV enc g.b) rows slots g.n)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30)
    (s0 : PState σ) (h0 : RI b g slots rows.length s0) :
    Stop (evaluateHOLFiniteState s0 (rowLoop g)).1 ∨ ((evaluateHOLFiniteState s0 (rowLoop g)).1 = none ∧
      RI b g slots rows.length (evaluateHOLFiniteState s0 (rowLoop g)).2 ∧
      (evaluateHOLFiniteState s0 (rowLoop g)).2.locals.lookup lJ0 =
        some (.val (.word (BitVec.ofNat 64 rows.length)))) := by
  have lC := hT.layC; have lS := hT.layS; have hle := hT.le
  have hC : g.C ≠ g.S + BitVec.ofNat 64 (8 * 0) ∧ True := ⟨fun e => by
    have := congrArg BitVec.toNat e; rw [toNat_add_of_lt _ _ (by have := g.S.isLt; omega)] at this; omega, trivial⟩
  have hCns : ∀ j, j < g.n → g.C ≠ g.S + BitVec.ofNat 64 (8 * j) := by
    intro j hj e
    have hpos : 0 < g.n := hinv.pos
    have hS : g.S.toNat + 8 * g.n < 2 ^ 64 := by have := hT.layR; have := hT.layD; have := hT.layK; omega
    have := congrArg BitVec.toNat e; rw [slot_toNat g hS j hj] at this; omega
  unfold rowLoop
  have hloop := while_stop (.cmp .lower (vv lJ0) (.load .one (.const g.C))) (rowBody g)
    (RI b g slots rows.length)
    (fun s => RI b g slots rows.length s ∧ s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 rows.length))))
    (fun s hs => by
      obtain ⟨had, _, _, _, _, _, i, hi, hI, _, hout⟩ := id hs
      have hcnt : T.EV s (.load .one (.const g.C)) = some (.val (.word (BitVec.ofNat 64 rows.length))) := by
        have := eval_load_word s _ _ (eval_const s g.C) (by rw [had]; exact hT.cnt.1)
        rw [hout _ hCns, hT.cnt.2] at this; exact this
      have hcmp : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .lower (vv lJ0) (.load .one (.const g.C))) = some (.val (.word (bw (i < rows.length)))) := by
        simp only [evalHOLFinite]
        rw [ConsLoop.eval_cmp_of s .lower _ _ _ _ (eval_vv s lJ0 _ hI) hcnt]
        have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length) ↔ i < rows.length := by
          rw [BitVec.lt_def]; simp; omega
        by_cases h : i < rows.length
        · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
        · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 rows.length := fun x => h (e.mp x)
          simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
      by_cases h : i < rows.length
      · refine ⟨1, by rw [hcmp]; simp [bw, h], fun e => absurd e (by decide), fun _ _ => ?_⟩
        rcases rowBody_spec b g enc rows ders slots hu hT hinv hn hb hcap (decClockHOLFinite s) hs i h hI with
          hst | ⟨hn', hri, -⟩
        · exact Or.inl hst
        · exact Or.inr ⟨hn', hri⟩
      · have hie : i = rows.length := by omega
        subst hie
        exact ⟨0, by rw [hcmp]; simp [bw], fun _ => ⟨hs, hI⟩, fun e => absurd rfl e⟩)
    s0 h0
  rcases hloop with hst | ⟨hn', hq, hj⟩
  · exact Or.inl hst
  · exact Or.inr ⟨hn', hq, hj⟩

/-- What the row clear leaves: zero slots, memory outside the slots as in `u`, locals outside `A` and `cj0`
as in `u`. -/
def RPost (u : PState σ) (g : VGeo) (A : List MlS) (s : PState σ) : Prop :=
  (∀ j, j < g.n → s.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word 0) ∧
  (∀ c, (∀ j, j < g.n → c ≠ g.S + BitVec.ofNat 64 (8 * j)) → s.memory c = u.memory c) ∧
  s.memaddrs = u.memaddrs ∧ s.code = u.code ∧ s.globals = u.globals ∧ s.topAddr = u.topAddr ∧
  (∀ y, y ≠ lJ0 → y ∉ A → s.locals.lookup y = u.locals.lookup y) ∧
  ∃ w, s.locals.lookup lJ0 = some (.val (.word w))

theorem rpost_dec (u : PState σ) (g : VGeo) (A : List MlS) (x : MlS) (hx : x ≠ lJ0) (body : ProgHOL 64)
    (h : Stop (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word 0)) u) body).1 ∨
      ((evaluateHOLFiniteState (setVarHOLFinite x (.val (.word 0)) u) body).1 = none ∧
        RPost (setVarHOLFinite x (.val (.word 0)) u) g (x :: A)
          (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word 0)) u) body).2)) :
    Stop (evaluateHOLFiniteState u (.dec x .one (.const 0) body)).1 ∨
      ((evaluateHOLFiniteState u (.dec x .one (.const 0) body)).1 = none ∧
        RPost u g A (evaluateHOLFiniteState u (.dec x .one (.const 0) body)).2) := by
  rw [dec_word_eq u x (.const 0) 0 body (eval_const u 0)]
  rcases h with h | ⟨hn, z, fr, ha, hc, hg, ht, hl, w, hw⟩
  · exact Or.inl h
  refine Or.inr ⟨hn, z, fr, ha, hc, hg, ht, fun y h1 h2 => ?_, w, ?_⟩
  · show (HolFiniteMapExact.resVarEq _ _).lookup y = _
    by_cases e : y = x
    · subst e; exact lookup_resVar_same _ _ _
    · rw [lookup_resVar_other _ _ _ _ e, hl y h1 (by simp [e, h2])]; exact lookup_setVar_other _ _ e
  · show (HolFiniteMapExact.resVarEq _ _).lookup lJ0 = _
    rw [lookup_resVar_other _ _ _ _ (Ne.symm hx)]; exact hw

/-- **The row clear**: stop, or every slot zero, memory outside the slots untouched, and only `cj0` among
the locals changed. -/
theorem rowClear_spec {α : Type} (u : PState σ) (g : VGeo) (enc : α → List (BitVec 64)) (rows : List α)
    (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat)
    (hT : VT u enc rows ders slots g hu) (hinv : ConsModel.Inv (homeV enc g.b) rows slots g.n)
    (hn : g.n = 2 ^ g.b) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (w0 : BitVec 64)
    (hw0 : u.locals.lookup lJ0 = some (.val (.word w0))) :
    Stop (evaluateHOLFiniteState u (rowClear g)).1 ∨ ((evaluateHOLFiniteState u (rowClear g)).1 = none ∧
      RPost u g [] (evaluateHOLFiniteState u (rowClear g)).2) := by
  unfold rowClear
  apply rpost_dec _ _ _ _ (by decide)
  apply rpost_dec _ _ _ _ (by decide)
  apply rpost_dec _ _ _ _ (by decide)
  apply rpost_dec _ _ _ _ (by decide)
  apply rpost_dec _ _ _ _ (by decide)
  apply rpost_dec _ _ _ _ (by decide)
  generalize hb' : setVarHOLFinite rV (.val (.word 0)) (setVarHOLFinite rJ (.val (.word 0))
    (setVarHOLFinite lWg (.val (.word 0)) (setVarHOLFinite lWh (.val (.word 0))
    (setVarHOLFinite lWn (.val (.word 0)) (setVarHOLFinite lWa (.val (.word 0)) u))))) = b
  have hbm : b.memory = u.memory := by rw [← hb']; rfl
  have hbd : b.memaddrs = u.memaddrs := by rw [← hb']; rfl
  have hbJ : b.locals.lookup lJ0 = some (.val (.word w0)) := by
    rw [← hb']; simp only [lookup_setVar_other _ _ (show lJ0 ≠ rV by decide), lookup_setVar_other _ _ (show lJ0 ≠ rJ by decide),
      lookup_setVar_other _ _ (show lJ0 ≠ lWg by decide), lookup_setVar_other _ _ (show lJ0 ≠ lWh by decide),
      lookup_setVar_other _ _ (show lJ0 ≠ lWn by decide), lookup_setVar_other _ _ (show lJ0 ≠ lWa by decide)]; exact hw0
  have hbt : ∀ y, y ∈ tmpR → ∃ w, b.locals.lookup y = some (.val (.word w)) := by
    intro y hy; rw [← hb']
    simp only [tmpR, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by lk⟩
  have hTb : VT b enc rows ders slots g hu := vt_of_eq hT hbm hbd
  rw [seq_normal _ (ConsLoop.assign_local b lJ0 (.const 0) 0 w0 (eval_const b 0) hbJ)]
  let s0 := setVarHOLFinite lJ0 (.val (.word 0)) b
  have h0 : RI b g slots rows.length s0 := by
    refine ⟨rfl, rfl, rfl, rfl, fun y hy _ => lookup_setVar_other _ _ hy, fun y hy => ?_, 0, Nat.zero_le _,
      lookup_setVar_same _ _ _, fun j hj => ?_, fun c _ => rfl⟩
    · rw [lookup_setVar_other _ _ (fun e => by subst e; exact absurd hy (by decide))]; exact hbt y hy
    · obtain ⟨v, hv, _, _, hm⟩ := hTb.slot j hj
      show b.memory _ = _; rw [hm]
      have : cur slots 0 j = v := by simp [cur, List.getD_eq_getElem?_getD, hv] <;> omega
      rw [this]
  rcases rowLoop_spec b g enc rows ders slots hu hTb hinv hn hb hcap s0 h0 with hst | ⟨hn', hri, hJ⟩
  · exact Or.inl hst
  obtain ⟨had, hcd, hgl, hta, hfr, -, i, hi, hI, hsl, hout⟩ := hri
  have hie : i = rows.length := by
    rw [hI] at hJ; simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hJ
    have := congrArg BitVec.toNat hJ; simp at this; have := hTb.le; have := hTb.layR; omega
  subst hie
  refine Or.inr ⟨hn', fun j hj => by rw [hsl j hj, cur_done hinv j]; rfl, hout, had, hcd, hgl, hta,
    fun y h1 h2 => hfr y h1 (by simpa [tmpR, or_comm, or_assoc, or_left_comm] using h2), _, hI⟩

end

end ConPanqueque.T
