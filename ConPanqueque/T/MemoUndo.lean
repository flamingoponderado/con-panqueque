import ConPanqueque.T.MemoPop
import ConPanqueque.T.MemoClear
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Undoing a memo's newest insert

`undoCode g ek rest`, inline at the table's static geometry `g`: the newest row (count `c`, row `c - 1`) must
hold the one-word key `ek` (else hang); a sweep of the slot array finds the slot holding `c` and zeroes it
(none found: hang); the count becomes `c - 1`.  The table then holds `m.erase k` (`memoAtG_pop`).
The temporary pushes of an inductive block's recursors (`classFeR`, `consBlockRecsTemp`) are undone this way,
newest first.
-/

namespace ConPanqueque.T

def slotJE (g : VGeo) : ExpHOL 64 := .op .add [.const g.S, .shift .lsl (vv lJ0) (.const 3)]

/-- Sweep the slots for the one holding the count; zero it and leave with `cj0 = n + 1`. -/
def scanLoop (g : VGeo) : ProgHOL 64 :=
  .while (.cmp .lower (vv lJ0) (.const (BitVec.ofNat 64 g.n)))
    (.ite (.cmp .equal (.load .one (slotJE g)) (.load .one (.const g.C)))
      (.seq (.store (slotJE g) (.const 0)) (.assign .local lJ0 (.const (BitVec.ofNat 64 (g.n + 1)))))
      (.assign .local lJ0 (.op .add [vv lJ0, .const 1])))

variable {σ : Type}

def ScanC (u s : PState σ) : Prop :=
  s.memaddrs = u.memaddrs ∧ s.code = u.code ∧ s.globals = u.globals ∧ s.topAddr = u.topAddr ∧
    (∀ y, y ≠ lJ0 → s.locals.lookup y = u.locals.lookup y)

/-- Found at `jf`: that slot held `wc` and is zeroed, all else as in `u`. -/
def ScanF (u : PState σ) (g : VGeo) (wc : BitVec 64) (s : PState σ) : Prop :=
  ∃ jf, jf < g.n ∧ u.memory (g.S + BitVec.ofNat 64 (8 * jf)) = .word wc ∧
    ∀ c, s.memory c = if c = g.S + BitVec.ofNat 64 (8 * jf) then .word 0 else u.memory c

def ScanI (u : PState σ) (g : VGeo) (wc : BitVec 64) (s : PState σ) : Prop :=
  ScanC u s ∧
  ((∃ j, j ≤ g.n ∧ s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) ∧ s.memory = u.memory) ∨
   (s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 (g.n + 1)))) ∧ ScanF u g wc s))

def ScanQ (u : PState σ) (g : VGeo) (wc : BitVec 64) (s : PState σ) : Prop :=
  ScanC u s ∧ (∃ w, s.locals.lookup lJ0 = some (.val (.word w))) ∧
    (s.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 (g.n + 1)))) → ScanF u g wc s)

theorem scanLoop_spec (u : PState σ) (g : VGeo) (wc : BitVec 64) (hn : g.n ≤ 2 ^ 56)
    (hS : g.S.toNat + 8 * g.n < 2 ^ 64)
    (hdom : ∀ j, j < g.n → u.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧
      ∃ v, u.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word v)
    (hCd : u.memaddrs g.C) (hCm : u.memory g.C = .word wc)
    (hj0 : u.locals.lookup lJ0 = some (.val (.word 0))) :
    Stop (evaluateHOLFiniteState u (scanLoop g)).1 ∨ ((evaluateHOLFiniteState u (scanLoop g)).1 = none ∧
      ScanQ u g wc (evaluateHOLFiniteState u (scanLoop g)).2) := by
  have hloop := while_stop _ _ (ScanI u g wc) (ScanQ u g wc)
    (fun s hs => by
      obtain ⟨hc, hcase⟩ := hs
      obtain ⟨hd, hcd, hg, hta, hl⟩ := hc
      rcases hcase with ⟨j, hjn, hj, hm⟩ | ⟨hj, hF⟩
      · have hcmp : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (vv lJ0) (.const (BitVec.ofNat 64 g.n))) = some (.val (.word (bw (j < g.n)))) := by
          simp only [evalHOLFinite]
          rw [ConsLoop.eval_cmp_of s .lower _ _ _ _ (eval_vv s lJ0 _ hj) (eval_const s _)]
          have e : (BitVec.ofNat 64 j < BitVec.ofNat 64 g.n) ↔ j < g.n := by
            rw [BitVec.lt_def]; simp; omega
          by_cases h : j < g.n
          · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]
          · have : ¬ BitVec.ofNat 64 j < BitVec.ofNat 64 g.n := fun x => h (e.mp x)
            simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
        by_cases h : j < g.n
        · refine ⟨1, by rw [hcmp]; simp [bw, h], fun e => absurd e (by decide), fun _ _ => ?_⟩
          let s1 := decClockHOLFinite s
          have hj1 : s1.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) := hj
          have hadr : g.S + BitVec.ofNat 64 j <<< (3 : BitVec 64).toNat = g.S + BitVec.ofNat 64 (8 * j) := by
            rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
          have hA : T.EV s1 (slotJE g) = some (.val (.word (g.S + BitVec.ofNat 64 (8 * j)))) := by
            rw [← hadr]; exact eval_add2 s1 _ _ _ _ (eval_const s1 _) (eval_shl s1 _ _ _ (eval_vv s1 lJ0 _ hj1) (by decide))
          obtain ⟨hdj, v, hv⟩ := hdom j h
          have hLs : T.EV s1 (.load .one (slotJE g)) = some (.val (.word v)) := by
            refine (eval_load_word s1 _ _ hA (by show s.memaddrs _; rw [hd]; exact hdj)).trans ?_
            show some (ValueHOL.val (s.memory _)) = _; rw [hm, hv]
          have hLc : T.EV s1 (.load .one (.const g.C)) = some (.val (.word wc)) := by
            refine (eval_load_word s1 _ _ (eval_const s1 _) (by show s.memaddrs _; rw [hd]; exact hCd)).trans ?_
            show some (ValueHOL.val (s.memory _)) = _; rw [hm, hCm]
          rw [ite_word s1 _ _ _ _ (ConsLoop.eval_cmp_of s1 .equal _ _ _ _ hLs hLc)]
          by_cases hvw : v = wc
          · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal v wc = true := by
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hvw]
            simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
            rw [seq_normal _ (store_word s1 _ _ _ 0 hA (eval_const s1 0) (by show s.memaddrs _; rw [hd]; exact hdj))]
            let s2 : PState σ :=
              { s1 with memory := fun c => (if c = g.S + BitVec.ofNat 64 (8 * j) then HolWordLab.word 0 else s1.memory c) }
            have hj2 : s2.locals.lookup lJ0 = some (.val (.word (BitVec.ofNat 64 j))) := hj
            rw [ConsLoop.assign_local s2 lJ0 _ (BitVec.ofNat 64 (g.n + 1)) _ (eval_const s2 _) hj2]
            refine Or.inr ⟨rfl, ⟨hd, hcd, hg, hta, fun y hy => by rw [lookup_setVar_other _ _ hy]; exact hl y hy⟩,
              Or.inr ⟨lookup_setVar_same _ _ _, j, h, by rw [hv, hvw], fun c => ?_⟩⟩
            show (if c = g.S + BitVec.ofNat 64 (8 * j) then _ else s.memory c) = _
            rw [hm]
          · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal v wc = false := by
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hvw]
            simp only [hc, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
            rw [ConsLoop.assign_local s1 lJ0 _ (BitVec.ofNat 64 (j + 1)) _
              (by rw [← word_add1_eq]; exact eval_add2 s1 _ _ _ _ (eval_vv s1 lJ0 _ hj1) (eval_const s1 1)) hj1]
            exact Or.inr ⟨rfl, ⟨hd, hcd, hg, hta, fun y hy => by rw [lookup_setVar_other _ _ hy]; exact hl y hy⟩,
              Or.inl ⟨j + 1, by omega, lookup_setVar_same _ _ _, hm⟩⟩
        · refine ⟨0, by rw [hcmp]; simp [bw, h], fun _ => ⟨⟨hd, hcd, hg, hta, hl⟩, ⟨_, hj⟩, fun hj' => ?_⟩,
            fun e => absurd rfl e⟩
          rw [hj] at hj'
          have e := congrArg BitVec.toNat (HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj hj')))
          simp at e; omega
      · have hcmp : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (vv lJ0) (.const (BitVec.ofNat 64 g.n))) = some (.val (.word 0)) := by
          simp only [evalHOLFinite]
          rw [ConsLoop.eval_cmp_of s .lower _ _ _ _ (eval_vv s lJ0 _ hj) (eval_const s _)]
          have : ¬ BitVec.ofNat 64 (g.n + 1) < BitVec.ofNat 64 g.n := by
            rw [BitVec.lt_def]; simp; omega
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
        exact ⟨0, hcmp, fun _ => ⟨⟨hd, hcd, hg, hta, hl⟩, ⟨_, hj⟩, fun _ => hF⟩, fun e => absurd rfl e⟩)
    u ⟨⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, Or.inl ⟨0, Nat.zero_le _, hj0, rfl⟩⟩
  exact hloop

def cntE (g : VGeo) : ExpHOL 64 := .load .one (.const g.C)
def lastRowE (g : VGeo) : ExpHOL 64 :=
  .op .add [.const g.R, .shift .lsl (.op .sub [cntE g, .const 1]) (.const 4)]

/-- Undo the newest insert of the table at `g`, whose key must be the one word `ek`; then `rest`. -/
def undoCode (g : VGeo) (ek : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .equal (cntE g) (.const 0)) hang
  (.ite (.cmp .notEqual (.load .one (.op .add [lastRowE g, .const 8])) (.const 1)) hang
  (.ite (.cmp .notEqual (.load .one (.load .one (lastRowE g))) ek) hang
  (.seq (.assign .local lJ0 (.const 0))
  (.seq (scanLoop g)
  (.ite (.cmp .notEqual (vv lJ0) (.const (BitVec.ofNat 64 (g.n + 1)))) hang
  (.seq (.store (.const g.C) (.op .sub [cntE g, .const 1])) rest))))))

/-- The undo on any one-tier table whose newest key is `k` (one word `w`): afterwards it holds `m.erase k`,
memory outside its region is untouched, and only `cj0` among the locals changed. -/
theorem undoCode_core {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
    {enc : K → List (BitVec 64)} {valW : V → BitVec 64} (hinj : ∀ x y, enc x = enc y → x = y)
    (t : PState σ) (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) (hm : MemoAtG enc valW t G g m)
    (k : K) (w : BitVec 64) (hk1 : enc k = [w]) (ek : ExpHOL 64) (hek : T.EV t ek = some (.val (.word w)))
    (rest : ProgHOL 64) (w0 : BitVec 64) (hw0 : t.locals.lookup lJ0 = some (.val (.word w0)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j))) :
    Stop (evaluateHOLFiniteState t (undoCode g ek rest)).1 ∨
    ∃ t4 : PState σ, evaluateHOLFiniteState t (undoCode g ek rest) = evaluateHOLFiniteState t4 rest ∧
      MemoAtG enc valW t4 G g (m.erase k) ∧ (∀ c, ¬ inR g c → t4.memory c = t.memory c) ∧
      t4.memaddrs = t.memaddrs ∧ t4.globals = t.globals ∧ t4.code = t.code ∧
      (∀ y, y ≠ lJ0 → t4.locals.lookup y = t.locals.lookup y) ∧ ∃ w, t4.locals.lookup lJ0 = some (.val (.word w)) := by
  have hm0 := hm
  obtain ⟨hdesc, hn, hb, hcap, tb, rows, ders, slots, hu, hT, hinv, hr, hder, hrel⟩ := hm0
  have lC := hT.layC; have lS := hT.layS; have lR := hT.layR; have lD := hT.layD; have lK := hT.layK
  have hle := hT.le
  have hn56 : g.n ≤ 2 ^ 56 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  have hpos : 0 < g.n := hinv.pos
  have hC : T.EV t (cntE g) = some (.val (.word (BitVec.ofNat 64 rows.length))) :=
    (eval_load_word t _ _ (eval_const t _) hT.cnt.1).trans (by rw [hT.cnt.2])
  unfold undoCode
  rw [ite_word t _ _ _ _ (ConsLoop.eval_cmp_of t .equal _ _ _ _ hC (eval_const t 0))]
  by_cases hc0 : rows.length = 0
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 rows.length) 0 = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hc0]
    simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (hang_stop _)
  have hne0 : BitVec.ofNat 64 rows.length ≠ 0 := fun e => by
    have := congrArg BitVec.toNat e; simp at this; omega
  have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 rows.length) 0 = false := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne0
  simp only [hc, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  -- the newest row
  have hi : rows.length - 1 < rows.length := by omega
  obtain ⟨P, hdR, hdR8, hmR, hmR8, hW, hP1, hP2⟩ := hT.row (rows.length - 1) hi
  have hsh := hT.short (rows.length - 1) hi
  have hsub : BitVec.ofNat 64 rows.length - 1 = BitVec.ofNat 64 (rows.length - 1) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  have hRow : T.EV t (lastRowE g) = some (.val (.word (g.R + BitVec.ofNat 64 (16 * (rows.length - 1))))) := by
    have e := eval_add2 t (.const g.R) (.shift .lsl (.op .sub [cntE g, .const 1]) (.const 4)) g.R _ (eval_const t g.R)
      (eval_shl t _ 4 _ (eval_sub2 t _ _ _ _ hC (eval_const t 1)) (by decide))
    rw [hsub, show (4 : BitVec 64).toNat = 4 from rfl, shl_ofNat _ _ (by omega)] at e
    exact e
  have hRow8 := eval_add2 t _ (.const 8) _ 8 hRow (eval_const t 8)
  have hL : T.EV t (.load .one (.op .add [lastRowE g, .const 8])) =
      some (.val (.word (BitVec.ofNat 64 (enc rows[rows.length - 1]).length))) :=
    (eval_load_word t _ _ hRow8 hdR8).trans (by rw [hmR8])
  rw [ite_word t _ _ _ _ (ConsLoop.eval_cmp_of t .notEqual _ _ _ _ hL (eval_const t 1))]
  rcases (Classical.em ((enc rows[rows.length - 1]).length = 1)).symm with hl1 | hl1
  · have hne : BitVec.ofNat 64 (enc rows[rows.length - 1]).length ≠ 1 := fun e => by
      have := congrArg BitVec.toNat e; simp at this; omega
    have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual
        (BitVec.ofNat 64 (enc rows[rows.length - 1]).length) 1 = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne
    simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (hang_stop _)
  have hc1 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual
      (BitVec.ofNat 64 (enc rows[rows.length - 1]).length) 1 = false := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl1]
  simp only [hc1, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  have hW0 := hW 0 (by omega)
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hW0
  have hK : T.EV t (.load .one (.load .one (lastRowE g))) =
      some (.val (.word (enc rows[rows.length - 1])[0])) :=
    (eval_load_word t _ _ ((eval_load_word t _ _ hRow hdR).trans (by rw [hmR])) hW0.1).trans (by rw [hW0.2])
  rw [ite_word t _ _ _ _ (ConsLoop.eval_cmp_of t .notEqual _ _ _ _ hK hek)]
  rcases (Classical.em ((enc rows[rows.length - 1])[0] = w)).symm with hx | hx
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (enc rows[rows.length - 1])[0] w = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hx]
    simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (hang_stop _)
  have hc2 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (enc rows[rows.length - 1])[0] w = false := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hx]
  simp only [hc2, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  have hencx : enc rows[rows.length - 1] = [w] := by
    apply List.ext_getElem (by simp [hl1])
    intro i h1 h2
    have : i = 0 := by simp at h2; omega
    subst this; simpa using hx
  have hxk : rows[rows.length - 1] = k := hinj _ _ (hencx.trans hk1.symm)
  -- the sweep
  rw [seq_normal _ (ConsLoop.assign_local t lJ0 (.const 0) 0 w0 (eval_const t 0) hw0)]
  let t5 := setVarHOLFinite lJ0 (.val (.word 0)) t
  rcases scanLoop_spec t5 g (BitVec.ofNat 64 rows.length) hn56 (by omega)
      (fun j hj => by
        obtain ⟨v, _, _, hma, hmv⟩ := hT.slot j hj
        exact ⟨hma, v, hmv⟩) hT.cnt.1 hT.cnt.2 (lookup_setVar_same _ _ _) with hs | ⟨hn6, hQ⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  have e6 : evaluateHOLFiniteState t5 (scanLoop g) = (none, (evaluateHOLFiniteState t5 (scanLoop g)).2) := by
    rw [← hn6]
  rw [seq_normal _ e6]
  generalize (evaluateHOLFiniteState t5 (scanLoop g)).2 = s6 at hQ
  obtain ⟨⟨hd6, hc6, hg6, hta6, hl6⟩, ⟨wl, hwl⟩, hF⟩ := hQ
  rw [ite_word s6 _ _ _ _ (ConsLoop.eval_cmp_of s6 .notEqual _ _ _ _ (eval_vv s6 lJ0 _ hwl) (eval_const s6 _))]
  rcases (Classical.em (wl = BitVec.ofNat 64 (g.n + 1))).symm with hwe | hwe
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual wl (BitVec.ofNat 64 (g.n + 1)) = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwe]
    simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (hang_stop _)
  have hc3 : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual wl (BitVec.ofNat 64 (g.n + 1)) = false := by
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwe]
  simp only [hc3, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  subst hwe
  obtain ⟨jf, hjf, hSj, hmem6⟩ := hF hwl
  have hSjN : (g.S + BitVec.ofNat 64 (8 * jf)).toNat = g.S.toNat + 8 * jf := toNat_add_of_lt _ _ (by omega)
  have hCne : g.C ≠ g.S + BitVec.ofNat 64 (8 * jf) := fun e => by
    have := congrArg BitVec.toNat e; rw [hSjN] at this; omega
  have hC6 : T.EV s6 (cntE g) = some (.val (.word (BitVec.ofNat 64 rows.length))) :=
    (eval_load_word s6 _ _ (eval_const s6 _) (by rw [hd6]; exact hT.cnt.1)).trans (by
      show some (ValueHOL.val (s6.memory g.C)) = _
      rw [hmem6]; simp only [hCne, ↓reduceIte]; show some (ValueHOL.val (t.memory g.C)) = _; rw [hT.cnt.2])
  rw [seq_normal _ (store_word s6 (.const g.C) _ g.C (BitVec.ofNat 64 rows.length - 1) (eval_const s6 _)
    (eval_sub2 s6 _ _ _ _ hC6 (eval_const s6 1)) (by rw [hd6]; exact hT.cnt.1))]
  let t7 : PState σ :=
    { s6 with memory := fun x => if x = g.C then .word (BitVec.ofNat 64 rows.length - 1) else s6.memory x }
  have hrest : ∀ x, x ≠ g.C → x ≠ g.S + BitVec.ofNat 64 (8 * jf) → t7.memory x = t.memory x := by
    intro x h1 h2
    show (if x = g.C then _ else s6.memory x) = _
    simp only [h1, ↓reduceIte]; rw [hmem6]; simp only [h2, ↓reduceIte]; rfl
  have hinC : inR g g.C := ⟨Nat.le_refl _, by omega⟩
  have hinS : inR g (g.S + BitVec.ofNat 64 (8 * jf)) := ⟨by rw [hSjN]; omega, by rw [hSjN]; omega⟩
  have hd7 : t7.memaddrs = t.memaddrs := by show s6.memaddrs = _; rw [hd6]; rfl
  refine Or.inr ⟨t7, rfl, ?_, fun c hc => hrest c (fun e => hc (e ▸ hinC)) (fun e => hc (e ▸ hinS)), hd7,
    by show s6.globals = _; rw [hg6]; rfl, by show s6.code = _; rw [hc6]; rfl,
    fun y hy => by show s6.locals.lookup y = _; rw [hl6 y hy]; exact lookup_setVar_other _ _ hy, ⟨_, hwl⟩⟩
  refine memoAtG_pop hinj hm k rows.length jf P (by omega) (by omega) hT.cnt.2 hmR
    (by rw [← hxk]; exact hmR8) (by rw [hk1]; simp) (by rw [← hxk]; exact hW) hjf hSj hd7 ?_ ?_ hrest
    (fun i hi => ⟨fun e => hGout i hi (e ▸ hinC), fun e => hGout i hi (e ▸ hinS)⟩)
  · show (if g.C = g.C then _ else _) = _; simp only [↓reduceIte, hsub]
  · show (if g.S + BitVec.ofNat 64 (8 * jf) = g.C then _ else s6.memory _) = _
    simp only [Ne.symm hCne, ↓reduceIte]; rw [hmem6]; simp only [↓reduceIte]

end ConPanqueque.T
