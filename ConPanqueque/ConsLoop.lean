import ConPanqueque.ConsModel
import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel

/-!
# The cons table's probe loop in Pancake

Slots are words at `S + 8j` (`0` empty, `i + 1` naming row `i`), rows are
two-word records at `R + 16i`, the key is two words `kf`, `ka`, and the table
has `n = mask + 1` slots (a power of two). `probeLoop` runs the model's `probe`
(`ConsModel`), and `probeLoop_spec` proves it: on exit `res` holds `i + 1` for
the model's hit `i`, or `0` for its miss.
-/

namespace ConPanqueque.ConsLoop

def lS := ofString "cs"
def lR := ofString "cr"
def lM := ofString "cm"
def lKf := ofString "kf"
def lKa := ofString "ka"
def lJ := ofString "cj"
def lC := ofString "cc"
def lG := ofString "cg"
def lRes := ofString "cres"
def lV := ofString "cv"
def vv (n : MlS) : ExpHOL 64 := .var .local n
def rowAddr : ExpHOL 64 := .op .add [vv lR, .shift .lsl (.op .sub [vv lV, .const 1]) (.const 4)]

/-- One step: out of fuel, an empty slot, a matching row, or the next slot. -/
def probeBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv lC) (.const 0)) (.assign .local lG (.const 0))
   (.seq (.assign .local lV (.load .one (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)])))
    (.ite (.cmp .equal (vv lV) (.const 0)) (.assign .local lG (.const 0))
     (.ite (.cmp .equal (.load .one rowAddr) (vv lKf))
       (.ite (.cmp .equal (.load .one (.op .add [rowAddr, .const 8])) (vv lKa))
         (.seq (.assign .local lRes (vv lV)) (.assign .local lG (.const 0)))
         (.seq (.assign .local lJ (.op .and [.op .add [vv lJ, .const 1], vv lM]))
           (.assign .local lC (.op .sub [vv lC, .const 1]))))
       (.seq (.assign .local lJ (.op .and [.op .add [vv lJ, .const 1], vv lM]))
         (.assign .local lC (.op .sub [vv lC, .const 1]))))))

def probeLoop : ProgHOL 64 := .while (vv lG) probeBody

section
variable {σ : Type} {α : Type} [DecidableEq α]

/-- The table's memory: slot words and row words, readable. -/
structure Mem (t : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (slots : List Nat) (n : Nat) (S R : BitVec 64) : Prop where
  slot : ∀ j (hj : j < n), ∃ v, slots[j]? = some v ∧ v < 2 ^ 60 ∧
    t.memaddrs (S + BitVec.ofNat 64 (8 * j)) ∧ t.memory (S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 v)
  row : ∀ i (hi : i < rows.length), t.memaddrs (R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (R + BitVec.ofNat 64 (16 * i) + 8) ∧
    t.memory (R + BitVec.ofNat 64 (16 * i)) = .word (enc rows[i]).1 ∧
    t.memory (R + BitVec.ofNat 64 (16 * i) + 8) = .word (enc rows[i]).2

/-- The loop's state: fixed inputs, and either still probing (the rest of the probe from `(f, j)`
is the answer) or done with the answer in `res`. -/
def LInv (t0 : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (slots : List Nat) (n : Nat) (S R : BitVec 64) (a : α) (ans : PR)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t0.memory ∧ u.memaddrs = t0.memaddrs ∧ u.code = t0.code ∧ u.globals = t0.globals ∧
  u.topAddr = t0.topAddr ∧
  u.locals.lookup lS = some (.val (.word S)) ∧ u.locals.lookup lR = some (.val (.word R)) ∧
  u.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1)))) ∧
  u.locals.lookup lKf = some (.val (.word (enc a).1)) ∧ u.locals.lookup lKa = some (.val (.word (enc a).2)) ∧
  (∀ y, y ≠ lJ → y ≠ lC → y ≠ lG → y ≠ lRes → y ≠ lV → u.locals.lookup y = t0.locals.lookup y) ∧
  ∃ f j, j < n ∧ u.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 f))) ∧
    u.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))) ∧ (∃ w, u.locals.lookup lV = some (.val (.word w))) ∧
    ((u.locals.lookup lG = some (.val (.word 1)) ∧ u.locals.lookup lRes = some (.val (.word 0)) ∧
        probeR rows slots n a f j = ans ∧ f ≤ n ∧ f + 1 ≤ u.clock ∧ t0.clock ≤ u.clock + (n - f)) ∨
     (u.locals.lookup lG = some (.val (.word 0)) ∧
        u.locals.lookup lRes = some (.val (.word (BitVec.ofNat 64 ((ans.toOpt.map (· + 1)).getD 0)))) ∧
        (∀ jj, ans = .empty jj → jj = j) ∧ (ans = .full ↔ f = 0) ∧ t0.clock ≤ u.clock + (n + 1)))

end

/-- Assigning a word to a local that already holds a word. -/
theorem assign_local {σ : Type} (u : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (w w0 : BitVec 64)
    (he : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e = some (.val (.word w)))
    (hx : u.locals.lookup x = some (.val (.word w0))) :
    evaluateHOLFiniteState u (.assign .local x e) = (none, setVarHOLFinite x (.val (.word w)) u) := by
  rw [assign_ok u .local x e _ he (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hx, shapeOfHOLExact, shapeEqHOL])]
  rfl

theorem and_mask (j b : Nat) (hb : b ≤ 60) (hj : j < 2 ^ b) :
    BitVec.ofNat 64 (j + 1) &&& BitVec.ofNat 64 (2 ^ b - 1) = BitVec.ofNat 64 ((j + 1) % 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ b ≤ 2 ^ 60 := Nat.pow_le_pow_right (by decide) hb
  have h2 : (2 : Nat) ^ 60 < 2 ^ 64 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := j + 1) (by omega), Nat.mod_eq_of_lt (a := 2 ^ b - 1) (by omega),
    Nat.mod_eq_of_lt (a := (j + 1) % 2 ^ b) (by have := Nat.mod_lt (j + 1) (Nat.two_pow_pos b); omega)]
  exact Nat.and_two_pow_sub_one_eq_mod (j + 1) b

theorem eval_cmp_of {σ : Type} (u : PanSemStateFiniteExact 64 σ) (op : Cmp) (l r : ExpHOL 64) (x y : BitVec 64)
    (hl : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) l = some (.val (.word x)))
    (hr : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) r = some (.val (.word y))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (.cmp op l r) =
      some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op x y then 1 else 0))) := by
  rw [evalHOLExact]; rw [hl, hr]

/-- A local's word value as a number (`0` if absent). -/
def wv {σ : Type} (u : PanSemStateFiniteExact 64 σ) (x : MlS) : Nat :=
  match u.locals.lookup x with
  | some (.val (.word w)) => w.toNat
  | _ => 0

theorem wv_of {σ : Type} {u : PanSemStateFiniteExact 64 σ} {x : MlS} {w : BitVec 64}
    (h : u.locals.lookup x = some (.val (.word w))) : wv u x = w.toNat := by simp [wv, h]

section
variable {σ : Type} {α : Type} [DecidableEq α]

theorem step (t0 : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (slots : List Nat) (n b : Nat) (S R : BitVec 64) (a : α) (ans : PR)
    (hn : n = 2 ^ b) (hb : b ≤ 60) (hmem : Mem t0 enc rows slots n S R)
    (hnamed : ∀ (j i : Nat), slots[j]? = some (i + 1) → i < rows.length) (hinj : ∀ x y, enc x = enc y → x = y)
    (u : PanSemStateFiniteExact 64 σ) (hI : LInv t0 enc rows slots n S R a ans u)
    (hgo : u.locals.lookup lG = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) probeBody = (none, u') ∧
      LInv t0 enc rows slots n S R a ans u' ∧ wv u' lC + wv u' lG < wv u lC + wv u lG := by
  obtain ⟨m0, d0, c0, g0, ta0, hlS, hlR, hlM, hlKf, hlKa, hfr, f, j, hj, hlC, hlJ, ⟨w, hlV⟩, br⟩ := hI
  obtain ⟨_, hlRes, hprobe, hfn, hclk, hclk0⟩ :=
    br.resolve_right (fun ⟨hlG0, _⟩ => by rw [hgo] at hlG0; cases hlG0)
  have hn60 : n ≤ 2 ^ 60 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  let v := decClockHOLFinite u
  have vloc : v.locals = u.locals := rfl
  have vmem : v.memory = u.memory := rfl
  have vmd : v.memaddrs = u.memaddrs := rfl
  have vck : v.clock = u.clock - 1 := rfl
  have hcmp0 : ∀ x, u.locals.lookup x = some (.val (.word (BitVec.ofNat 64 f))) →
      @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a)) (.cmp .equal (vv x) (.const 0)) =
        some (.val (.word (if f = 0 then 1 else 0))) := by
    intro x hx
    simp [vv, evalHOLExact, vloc, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hf : f = 0
    · simp [hf]
    · have : ¬ BitVec.ofNat 64 f = 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [hf]; exact this
  have setG : ∀ (x : MlS) (z : BitVec 64), x ≠ lG →
      (setVarHOLFinite lG (.val (.word z)) v).locals.lookup x = u.locals.lookup x := by
    intro x z hx; rw [lookup_setVar_other _ _ hx]; rfl
  unfold probeBody
  rw [ite_word v _ _ _ _ (hcmp0 lC hlC)]
  by_cases hf0 : f = 0
  · subst hf0
    simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [assign_local v lG (.const 0) 0 1 (by simp [evalHOLExact]) (by rw [vloc]; exact hgo)]
    refine ⟨_, rfl, ?_, ?_⟩
    · refine ⟨m0, d0, c0, g0, ta0, by rw [setG _ _ (by decide)]; exact hlS, by rw [setG _ _ (by decide)]; exact hlR,
        by rw [setG _ _ (by decide)]; exact hlM, by rw [setG _ _ (by decide)]; exact hlKf,
        by rw [setG _ _ (by decide)]; exact hlKa,
        fun y a1 a2 a3 a4 a5 => by rw [setG _ _ a3]; exact hfr y a1 a2 a3 a4 a5,
        0, j, hj, by rw [setG _ _ (by decide)]; exact hlC,
        by rw [setG _ _ (by decide)]; exact hlJ, ⟨w, by rw [setG _ _ (by decide)]; exact hlV⟩,
        Or.inr ⟨lookup_setVar_same _ _ _, ?_, ?_, ?_, ?_⟩⟩
      · rw [setG _ _ (by decide), hlRes, ← hprobe]; simp [probeR, PR.toOpt]
      · intro jj e; rw [← hprobe] at e; simp [probeR] at e
      · exact ⟨fun _ => rfl, fun _ => by rw [← hprobe]; simp [probeR]⟩
      · show t0.clock ≤ u.clock - 1 + (n + 1); omega
    · rw [wv_of (lookup_setVar_same _ _ _), wv_of hgo,
        wv_of (show (setVarHOLFinite lG (.val (.word 0)) v).locals.lookup lC = _ by rw [setG _ _ (by decide)]; exact hlC),
        wv_of hlC]
      simp
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [show ¬ (f' + 1 = 0) from by omega, ↓reduceIte, ne_eq, not_true_eq_false]
  -- load the slot
  obtain ⟨vs, hvs, hvs60, hsd, hsm⟩ := hmem.slot j hj
  have hsaddr : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)]) = some (.val (.word (S + BitVec.ofNat 64 (8 * j)))) := by
    simp [vv, evalHOLExact, evalListHOLExact, vloc, hlS, hlJ, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hload : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)])) = some (.val (.word (BitVec.ofNat 64 vs))) := by
    rw [eval_load_word v _ _ hsaddr (by rw [vmd, d0]; exact hsd)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, hsm]
  rw [seq_normal _ (assign_local v lV _ _ w hload (by rw [vloc]; exact hlV))]
  let v1 := setVarHOLFinite lV (.val (.word (BitVec.ofNat 64 vs))) v
  have set1 : ∀ (x : MlS), x ≠ lV → v1.locals.lookup x = u.locals.lookup x := by
    intro x hx; simp only [v1]; rw [lookup_setVar_other _ _ hx]; rfl
  have hv1V : v1.locals.lookup lV = some (.val (.word (BitVec.ofNat 64 vs))) := lookup_setVar_same _ _ _
  have hvsw : (BitVec.ofNat 64 vs).toNat = vs := by simp; omega
  -- a finished state: `go := 0` (and possibly `res := r`) from a state with `u`'s other locals
  have fin : ∀ (x : PanSemStateFiniteExact 64 σ) (r : BitVec 64),
      x.memory = u.memory → x.memaddrs = u.memaddrs → x.code = u.code → x.globals = u.globals →
      x.topAddr = u.topAddr → x.clock = u.clock - 1 →
      (∀ y, y ≠ lG → y ≠ lRes → y ≠ lV → x.locals.lookup y = u.locals.lookup y) →
      (∃ w', x.locals.lookup lV = some (.val (.word w'))) →
      x.locals.lookup lG = some (.val (.word 0)) → x.locals.lookup lRes = some (.val (.word r)) →
      r = BitVec.ofNat 64 ((ans.toOpt.map (· + 1)).getD 0) → (∀ jj, ans = .empty jj → jj = j) →
      (∀ hfull' : ans = .full, False) →
      LInv t0 enc rows slots n S R a ans x ∧ wv x lC + wv x lG < wv u lC + wv u lG := by
    intro x r xm xd xc xg xt xk xl xv xg0 xr hr hemp hnf
    have hfull' : ans ≠ .full := fun e => hnf e
    have lk : ∀ y, y ≠ lG → y ≠ lRes → y ≠ lV → x.locals.lookup y = u.locals.lookup y := xl
    refine ⟨⟨by rw [xm, m0], by rw [xd, d0], by rw [xc, c0], by rw [xg, g0], by rw [xt, ta0],
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlS, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlR,
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlM, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlKf,
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlKa,
      fun y a1 a2 a3 a4 a5 => by rw [lk _ a3 a4 a5]; exact hfr y a1 a2 a3 a4 a5, f' + 1, j, hj,
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlC, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlJ,
      xv, Or.inr ⟨xg0, by rw [xr, hr], hemp, ⟨fun e => absurd e hfull', fun e => by omega⟩,
        by rw [xk]; omega⟩⟩, ?_⟩
    rw [wv_of xg0, wv_of hgo, wv_of (show x.locals.lookup lC = _ by rw [lk _ (by decide) (by decide) (by decide)]; exact hlC),
      wv_of hlC]
    simp
  have hcmpv : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.cmp .equal (vv lV) (.const 0)) = some (.val (.word (if vs = 0 then 1 else 0))) := by
    simp [vv, evalHOLExact, hv1V, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h0 : vs = 0
    · simp [h0]
    · have : ¬ BitVec.ofNat 64 vs = 0 := fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega)
      simp [h0]; exact this
  rw [ite_word v1 _ _ _ _ hcmpv]
  by_cases hv0 : vs = 0
  · subst hv0
    simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [assign_local v1 lG (.const 0) 0 1 (by simp [evalHOLExact]) (by rw [set1 _ (by decide)]; exact hgo)]
    have hans : ans = .empty j := by rw [← hprobe]; simp [probeR, hvs]
    obtain ⟨hfl, hfr⟩ := fin (setVarHOLFinite lG (.val (.word 0)) v1) 0 rfl rfl rfl rfl rfl rfl
      (fun y h1 h2 h3 => by rw [lookup_setVar_other _ _ h1, set1 _ h3])
      ⟨_, by rw [lookup_setVar_other _ _ (by decide)]; exact hv1V⟩ (lookup_setVar_same _ _ _)
      (by rw [lookup_setVar_other _ _ (by decide), set1 _ (by decide)]; exact hlRes) (by rw [hans]; rfl)
      (by intro jj e; rw [hans] at e; cases e; rfl) (fun e => by rw [hans] at e; cases e)
    exact ⟨_, rfl, hfl, hfr⟩
  obtain ⟨i, rfl⟩ : ∃ i, vs = i + 1 := ⟨vs - 1, by omega⟩
  simp only [show ¬ (i + 1 = 0) from by omega, ↓reduceIte, ne_eq, not_true_eq_false]
  have hi := hnamed j i hvs
  obtain ⟨rd1, rd2, rm1, rm2⟩ := hmem.row i hi
  have hraddr : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a)) rowAddr =
      some (.val (.word (R + BitVec.ofNat 64 (16 * i)))) := by
    simp [rowAddr, vv, evalHOLExact, evalListHOLExact, hv1V, set1 lR (by decide), hlR, wordOpHOL, wordOp, valueIsWord,
      valueWord, wordShiftHOL]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_sub, Nat.shiftLeft_eq]; omega
  have hl1 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a)) (.load .one rowAddr) =
      some (.val (.word (enc rows[i]).1)) := by
    rw [eval_load_word v1 _ _ hraddr (by show u.memaddrs _; rw [d0]; exact rd1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, rm1]
  have hl2 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.load .one (.op .add [rowAddr, .const 8])) = some (.val (.word (enc rows[i]).2)) := by
    rw [eval_load_word v1 _ (R + BitVec.ofNat 64 (16 * i) + 8)
      (by simp only [evalHOLExact, evalListHOLExact]; rw [hraddr]; simp [wordOpHOL, wordOp, valueIsWord, valueWord])
      (by show u.memaddrs _; rw [d0]; exact rd2)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, rm2]
  have hKf1 : v1.locals.lookup lKf = some (.val (.word (enc a).1)) := by rw [set1 _ (by decide)]; exact hlKf
  have hKa1 : v1.locals.lookup lKa = some (.val (.word (enc a).2)) := by rw [set1 _ (by decide)]; exact hlKa
  -- advancing to the next slot
  have adv : rows[i] ≠ a → ∃ u', evaluateHOLFiniteState v1
      (.seq (.assign .local lJ (.op .and [.op .add [vv lJ, .const 1], vv lM])) (.assign .local lC (.op .sub [vv lC, .const 1])))
      = (none, u') ∧ LInv t0 enc rows slots n S R a ans u' ∧ wv u' lC + wv u' lG < wv u lC + wv u lG := by
    intro hne
    have hj1 : v1.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))) := by rw [set1 _ (by decide)]; exact hlJ
    have hM1 : v1.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1)))) := by rw [set1 _ (by decide)]; exact hlM
    have hjn : j < 2 ^ b := by rw [← hn]; exact hj
    have ej := assign_local v1 lJ (.op .and [.op .add [vv lJ, .const 1], vv lM]) (BitVec.ofNat 64 ((j + 1) % n))
      (BitVec.ofNat 64 j)
      (by simp [vv, evalHOLExact, evalListHOLExact, hj1, hM1, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hn]; rw [← and_mask j b hb hjn]; congr 1
          · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
          · show _ &&& (18446744073709551615#64) = _
            rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]) hj1
    rw [seq_normal _ ej]
    let v2 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 ((j + 1) % n)))) v1
    have hC2 : v2.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 (f' + 1)))) := by
      simp only [v2]; rw [lookup_setVar_other _ _ (by decide), set1 _ (by decide)]; exact hlC
    rw [assign_local v2 lC (.op .sub [vv lC, .const 1]) (BitVec.ofNat 64 f') _
      (by simp [vv, evalHOLExact, evalListHOLExact, hC2, wordOpHOL, wordOp, valueIsWord, valueWord]
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) hC2]
    let u' := setVarHOLFinite lC (.val (.word (BitVec.ofNat 64 f'))) v2
    have lk : ∀ y, y ≠ lC → y ≠ lJ → y ≠ lV → u'.locals.lookup y = u.locals.lookup y := by
      intro y h1 h2 h3; simp only [u', v2]; rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, set1 _ h3]
    have hrowne : rows[i]? ≠ some a := by simp [hi]; exact hne
    have hstep : probeR rows slots n a (f' + 1) j = probeR rows slots n a f' ((j + 1) % n) := by
      simp [probeR, hvs, hrowne]
    refine ⟨u', rfl, ⟨m0, d0, c0, g0, ta0, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlS,
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlR, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlM,
      by rw [lk _ (by decide) (by decide) (by decide)]; exact hlKf, by rw [lk _ (by decide) (by decide) (by decide)]; exact hlKa,
      fun y a1 a2 a3 a4 a5 => by rw [lk _ a2 a1 a5]; exact hfr y a1 a2 a3 a4 a5,
      f', (j + 1) % n, Nat.mod_lt _ (by omega), lookup_setVar_same _ _ _,
      by simp only [u']; rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _,
      ⟨_, by simp only [u', v2]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact hv1V⟩,
      Or.inl ⟨by rw [lk _ (by decide) (by decide) (by decide)]; exact hgo,
        by rw [lk _ (by decide) (by decide) (by decide)]; exact hlRes, by rw [← hstep]; exact hprobe, by omega,
        by show f' + 1 ≤ u.clock - 1; omega, by show t0.clock ≤ u.clock - 1 + (n - f'); omega⟩⟩, ?_⟩
    rw [wv_of (lookup_setVar_same _ _ _), wv_of (show u'.locals.lookup lG = _ by rw [lk _ (by decide) (by decide) (by decide)]; exact hgo),
      wv_of hlC, wv_of hgo]
    simp; omega
  have hc1 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.cmp .equal (.load .one rowAddr) (vv lKf)) =
      some (.val (.word (if (enc rows[i]).1 = (enc a).1 then 1 else 0))) := by
    rw [eval_cmp_of v1 .equal _ _ _ (enc a).1 hl1 (by simp [vv, evalHOLExact, hKf1])]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [ite_word v1 _ _ _ _ hc1]
  by_cases e1 : (enc rows[i]).1 = (enc a).1
  · simp only [e1, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc2 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.cmp .equal (.load .one (.op .add [rowAddr, .const 8])) (vv lKa)) =
        some (.val (.word (if (enc rows[i]).2 = (enc a).2 then 1 else 0))) := by
      rw [eval_cmp_of v1 .equal _ _ _ (enc a).2 hl2 (by simp [vv, evalHOLExact, hKa1])]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [ite_word v1 _ _ _ _ hc2]
    by_cases e2 : (enc rows[i]).2 = (enc a).2
    · simp only [e2, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have heq : rows[i] = a := hinj _ _ (Prod.ext e1 e2)
      have hans : ans = .hit i := by rw [← hprobe]; simp [probeR, hvs, hi, heq]
      have hres1 : v1.locals.lookup lRes = some (.val (.word 0)) := by rw [set1 _ (by decide)]; exact hlRes
      rw [seq_normal _ (assign_local v1 lRes (vv lV) (BitVec.ofNat 64 (i + 1)) 0 (by simp [vv, evalHOLExact, hv1V]) hres1)]
      let v2 := setVarHOLFinite lRes (.val (.word (BitVec.ofNat 64 (i + 1)))) v1
      have hG2 : v2.locals.lookup lG = some (.val (.word 1)) := by
        simp only [v2]; rw [lookup_setVar_other _ _ (by decide), set1 _ (by decide)]; exact hgo
      rw [assign_local v2 lG (.const 0) 0 1 (by simp [evalHOLExact]) hG2]
      obtain ⟨hfl, hfr⟩ := fin (setVarHOLFinite lG (.val (.word 0)) v2) (BitVec.ofNat 64 (i + 1)) rfl rfl rfl rfl rfl rfl
        (fun y h1 h2 h3 => by rw [lookup_setVar_other _ _ h1]; simp only [v2]; rw [lookup_setVar_other _ _ h2, set1 _ h3])
        ⟨_, by rw [lookup_setVar_other _ _ (by decide)]; simp only [v2]; rw [lookup_setVar_other _ _ (by decide)]; exact hv1V⟩
        (lookup_setVar_same _ _ _)
        (by rw [lookup_setVar_other _ _ (by decide)]; exact lookup_setVar_same _ _ _) (by rw [hans]; rfl)
        (by intro jj e; rw [hans] at e; cases e) (fun e => by rw [hans] at e; cases e)
      exact ⟨_, rfl, hfl, hfr⟩
    · simp only [e2, ↓reduceIte, ne_eq, not_true_eq_false]
      exact adv (fun h => e2 (by rw [h]))
  · simp only [e1, ↓reduceIte, ne_eq, not_true_eq_false]
    exact adv (fun h => e1 (by rw [h]))


theorem probeLoop_spec (t0 : PanSemStateFiniteExact 64 σ) (enc : α → BitVec 64 × BitVec 64) (rows : List α)
    (slots : List Nat) (n b : Nat) (S R : BitVec 64) (a : α) (ans : PR)
    (hn : n = 2 ^ b) (hb : b ≤ 60) (hmem : Mem t0 enc rows slots n S R)
    (hnamed : ∀ (j i : Nat), slots[j]? = some (i + 1) → i < rows.length) (hinj : ∀ x y, enc x = enc y → x = y)
    (hI : LInv t0 enc rows slots n S R a ans t0) :
    ∃ t', evaluateHOLFiniteState t0 probeLoop = (none, t') ∧ LInv t0 enc rows slots n S R a ans t' ∧
      t'.locals.lookup lG = some (.val (.word 0)) := by
  have := while_rule (vv lG) probeBody (LInv t0 enc rows slots n S R a ans) (fun u => wv u lC + wv u lG)
    (fun u => LInv t0 enc rows slots n S R a ans u ∧ u.locals.lookup lG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, f, j, hj, hlC, hlJ, hlV, br⟩ := id hu
      rcases br with ⟨hgo, hres, hpr, hfn, hclk, hclk0⟩ | ⟨hg0, hres, hemp, hfu, hclk0⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hgo], fun h => absurd h (by decide), fun _ => ?_⟩
        have hn60 : n ≤ 2 ^ 60 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
        refine ⟨by rw [wv_of hlC, wv_of hgo]; simp; omega, by rw [wv_of hgo]; simp, ?_⟩
        exact step t0 enc rows slots n b S R a ans hn hb hmem hnamed hinj u hu hgo
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg0], fun _ => ⟨hu, hg0⟩, fun h => absurd rfl h⟩)
    t0 hI
  obtain ⟨t', ev, hQ, hg⟩ := this
  exact ⟨t', ev, hQ, hg⟩
end

end ConPanqueque.ConsLoop
