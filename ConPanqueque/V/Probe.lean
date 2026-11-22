import ConPanqueque.V.Key
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel

/-!
# The generic cons table's probe loop

Slots are words at `S + 8j` (`0` empty, `i + 1` naming row `i`). Row `i` is a
two-word record at `R + 16i`: a pointer to its key words and their count. The
key being probed is `vl` words at `vk`. A slot's row is a hit when the counts
agree and `cmpLoop` finds the words equal. `probeLoop_spec`: stop, or the
model's `probeR` answer (`ConsModel`).
-/

namespace ConPanqueque.V

def lS := ofString "cs"
def lR := ofString "cr"
def lM := ofString "cm"
def lK := ofString "vk"
def lL := ofString "vl"
def lJ := ofString "cj"
def lC := ofString "cc"
def lG := ofString "cg"
def lRes := ofString "cres"
def lV := ofString "cv"

/-- The locals the probe writes. -/
def scr : List MlS := [lJ, lC, lG, lRes, lV, lWa, lWb, lWn, lWeq, lWg]
/-- The comparison loop's locals. -/
def cscr : List MlS := [lWa, lWb, lWn, lWeq, lWg]

def rowAddr : ExpHOL 64 := .op .add [vv lR, .shift .lsl (.op .sub [vv lV, .const 1]) (.const 4)]

def nextP : ProgHOL 64 :=
  .seq (.assign .local lJ (.op .and [.op .add [vv lJ, .const 1], vv lM])) (.assign .local lC (.op .sub [vv lC, .const 1]))

def cmpSetup : ProgHOL 64 :=
  .seq (.assign .local lWa (.load .one rowAddr))
   (.seq (.assign .local lWb (vv lK))
    (.seq (.assign .local lWn (vv lL))
     (.seq (.assign .local lWeq (.const 1)) (.assign .local lWg (.const 1)))))

def probeBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv lC) (.const 0)) (.assign .local lG (.const 0))
   (.seq (.assign .local lV (.load .one (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)])))
    (.ite (.cmp .equal (vv lV) (.const 0)) (.assign .local lG (.const 0))
     (.ite (.cmp .equal (.load .one (.op .add [rowAddr, .const 8])) (vv lL))
       (.seq cmpSetup (.seq cmpLoop
         (.ite (vv lWeq) (.seq (.assign .local lRes (vv lV)) (.assign .local lG (.const 0))) nextP)))
       nextP)))

def probeLoop : ProgHOL 64 := .while (vv lG) probeBody

section
variable {σ : Type} {α : Type} [DecidableEq α]

/-- The table's memory: slot words, and each row's key pointer and count, the key words there. -/
structure VMem (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α)
    (slots : List Nat) (n : Nat) (S R : BitVec 64) : Prop where
  slot : ∀ j (hj : j < n), ∃ v, slots[j]? = some v ∧ v < 2 ^ 60 ∧
    t.memaddrs (S + BitVec.ofNat 64 (8 * j)) ∧ t.memory (S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 v)
  row : ∀ i (hi : i < rows.length), ∃ P, t.memaddrs (R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (R + BitVec.ofNat 64 (16 * i) + 8) ∧ t.memory (R + BitVec.ofNat 64 (16 * i)) = .word P ∧
    t.memory (R + BitVec.ofNat 64 (16 * i) + 8) = .word (BitVec.ofNat 64 (enc rows[i]).length) ∧
    Words t P (enc rows[i])
  short : ∀ i (hi : i < rows.length), (enc rows[i]).length < 2 ^ 61

/-- What every state of the probe keeps: `t0`'s memory and fixed locals, other locals as in `t0`,
and the comparison locals holding words. -/
structure Base (t0 u : PanSemStateFiniteExact 64 σ) (n : Nat) (S R K : BitVec 64) (L : Nat) : Prop where
  mem : u.memory = t0.memory
  addrs : u.memaddrs = t0.memaddrs
  code : u.code = t0.code
  globals : u.globals = t0.globals
  top : u.topAddr = t0.topAddr
  s : u.locals.lookup lS = some (.val (.word S))
  r : u.locals.lookup lR = some (.val (.word R))
  m : u.locals.lookup lM = some (.val (.word (BitVec.ofNat 64 (n - 1))))
  k : u.locals.lookup lK = some (.val (.word K))
  l : u.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 L)))
  fr : ∀ y, y ∉ scr → u.locals.lookup y = t0.locals.lookup y
  cw : ∀ y, y ∈ cscr → ∃ w, u.locals.lookup y = some (.val (.word w))

theorem base_dec {t0 u : PanSemStateFiniteExact 64 σ} {n : Nat} {S R K : BitVec 64} {L : Nat}
    (h : Base t0 u n S R K L) : Base t0 (decClockHOLFinite u) n S R K L :=
  ⟨h.mem, h.addrs, h.code, h.globals, h.top, h.s, h.r, h.m, h.k, h.l, h.fr, h.cw⟩

theorem base_set {t0 u : PanSemStateFiniteExact 64 σ} {n : Nat} {S R K : BitVec 64} {L : Nat}
    (h : Base t0 u n S R K L) (x : MlS) (hx : x ∈ scr) (w : BitVec 64) :
    Base t0 (setVarHOLFinite x (.val (.word w)) u) n S R K L := by
  have ne : ∀ y, y ∉ scr → y ≠ x := fun y hy e => hy (e ▸ hx)
  refine ⟨h.mem, h.addrs, h.code, h.globals, h.top, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [lookup_setVar_other _ _ (ne _ (by decide))]; exact h.s
  · rw [lookup_setVar_other _ _ (ne _ (by decide))]; exact h.r
  · rw [lookup_setVar_other _ _ (ne _ (by decide))]; exact h.m
  · rw [lookup_setVar_other _ _ (ne _ (by decide))]; exact h.k
  · rw [lookup_setVar_other _ _ (ne _ (by decide))]; exact h.l
  · rw [lookup_setVar_other _ _ (ne _ hy)]; exact h.fr y hy
  · by_cases e : y = x
    · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
    · rw [lookup_setVar_other _ _ e]; exact h.cw y hy

/-- The probe's invariant: `f` slots of fuel left at slot `j`, still going or done. -/
def LInv (t0 : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α) (slots : List Nat) (n : Nat)
    (S R K : BitVec 64) (a : α) (ans : PR) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  Base t0 u n S R K (enc a).length ∧
  ∃ f j, j < n ∧ u.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 f))) ∧
    u.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))) ∧ (∃ w, u.locals.lookup lV = some (.val (.word w))) ∧
    ((u.locals.lookup lG = some (.val (.word 1)) ∧ u.locals.lookup lRes = some (.val (.word 0)) ∧
        probeR rows slots n a f j = ans ∧ f ≤ n) ∨
     (u.locals.lookup lG = some (.val (.word 0)) ∧
        u.locals.lookup lRes = some (.val (.word (BitVec.ofNat 64 ((ans.toOpt.map (· + 1)).getD 0)))) ∧
        (∀ jj, ans = .empty jj → jj = j) ∧ (ans = .full ↔ f = 0)))

end

section
variable {σ : Type} {α : Type} [DecidableEq α]

theorem bw_ofNat (f : Nat) (hf : f < 2 ^ 64) : bw (BitVec.ofNat 64 f = 0) = bw (f = 0) := by
  by_cases h : f = 0
  · subst h; rfl
  · have : ¬ BitVec.ofNat 64 f = 0 := fun e => h (by have := congrArg BitVec.toNat e; simp at this; omega)
    simp [bw, h]; exact this

theorem eval_slotAddr (s : PanSemStateFiniteExact 64 σ) (S : BitVec 64) (j : Nat) (hj : j < 2 ^ 60)
    (hs : s.locals.lookup lS = some (.val (.word S)))
    (hJ : s.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j)))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)]) = some (.val (.word (S + BitVec.ofNat 64 (8 * j)))) := by
  simp [vv, evalHOLExact, evalListHOLExact, hs, hJ, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem eval_rowAddr (s : PanSemStateFiniteExact 64 σ) (R : BitVec 64) (i : Nat) (hi : i + 1 < 2 ^ 60)
    (hr : s.locals.lookup lR = some (.val (.word R)))
    (hV : s.locals.lookup lV = some (.val (.word (BitVec.ofNat 64 (i + 1))))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) rowAddr =
      some (.val (.word (R + BitVec.ofNat 64 (16 * i)))) := by
  simp [rowAddr, vv, evalHOLExact, evalListHOLExact, hV, hr, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_sub, Nat.shiftLeft_eq]; omega

theorem eval_eq0 (u : PanSemStateFiniteExact 64 σ) (x : MlS) (f : Nat) (hf : f < 2 ^ 64)
    (h : u.locals.lookup x = some (.val (.word (BitVec.ofNat 64 f)))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (.cmp .equal (vv x) (.const 0)) =
      some (.val (.word (bw (f = 0)))) := by
  rw [ConsLoop.eval_cmp_of u .equal _ _ _ 0 (eval_vv u x _ h) (by simp [evalHOLExact]), ← bw_ofNat f hf]
  simp [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Moving to the next slot after a non-matching row. -/
theorem adv (t0 : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α) (slots : List Nat)
    (n b : Nat) (S R K : BitVec 64) (a : α) (ans : PR) (hn : n = 2 ^ b) (hb : b ≤ 60)
    (x : PanSemStateFiniteExact 64 σ) (hB : Base t0 x n S R K (enc a).length) (f j : Nat) (hj : j < n)
    (hC : x.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 (f + 1)))))
    (hJ : x.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))))
    (hV : ∃ w, x.locals.lookup lV = some (.val (.word w)))
    (hG : x.locals.lookup lG = some (.val (.word 1))) (hRes : x.locals.lookup lRes = some (.val (.word 0)))
    (hpr : probeR rows slots n a f ((j + 1) % n) = ans) (hf : f + 1 ≤ n) :
    ∃ u', evaluateHOLFiniteState x nextP = (none, u') ∧ LInv t0 enc rows slots n S R K a ans u' := by
  have hjn : j < 2 ^ b := by rw [← hn]; exact hj
  unfold nextP
  rw [seq_normal _ (ConsLoop.assign_local x lJ _ (BitVec.ofNat 64 ((j + 1) % n)) _
    (by simp [vv, evalHOLExact, evalListHOLExact, hJ, hB.m, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hn]; rw [← ConsLoop.and_mask j b hb hjn]; congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
        · show _ &&& (18446744073709551615#64) = _
          rw [show (18446744073709551615#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]) hJ)]
  let x1 := setVarHOLFinite lJ (.val (.word (BitVec.ofNat 64 ((j + 1) % n)))) x
  have hC1 : x1.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 (f + 1)))) := by lk [x1]; exact hC
  rw [ConsLoop.assign_local x1 lC _ (BitVec.ofNat 64 f) _
    (by rw [eval_sub_c x1 lC _ _ hC1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) hC1]
  obtain ⟨w, hV⟩ := hV
  exact ⟨_, rfl, base_set (base_set hB _ (by decide) _) _ (by decide) _, f, (j + 1) % n, Nat.mod_lt _ (by omega),
    by lk, by lk [x1], ⟨w, by lk [x1]; exact hV⟩, Or.inl ⟨by lk [x1]; exact hG, by lk [x1]; exact hRes, hpr, by omega⟩⟩

theorem probe_step (t0 : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α)
    (slots : List Nat) (n b : Nat) (S R K : BitVec 64) (a : α) (ans : PR)
    (hn : n = 2 ^ b) (hb : b ≤ 60) (hmem : VMem t0 enc rows slots n S R) (hK : Words t0 K (enc a))
    (hKl : (enc a).length < 2 ^ 61)
    (hnamed : ∀ (j i : Nat), slots[j]? = some (i + 1) → i < rows.length) (hinj : ∀ x y, enc x = enc y → x = y)
    (u : PanSemStateFiniteExact 64 σ) (hI : LInv t0 enc rows slots n S R K a ans u)
    (hgo : u.locals.lookup lG = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState (decClockHOLFinite u) probeBody).1 ∨
      ((evaluateHOLFiniteState (decClockHOLFinite u) probeBody).1 = none ∧
        LInv t0 enc rows slots n S R K a ans (evaluateHOLFiniteState (decClockHOLFinite u) probeBody).2) := by
  obtain ⟨hB, f, j, hj, hlC, hlJ, hlV, br⟩ := hI
  obtain ⟨_, hlRes, hprobe, hfn⟩ := br.resolve_right (fun ⟨hlG0, _⟩ => by rw [hgo] at hlG0; cases hlG0)
  have hn60 : n ≤ 2 ^ 60 := by rw [hn]; exact Nat.pow_le_pow_right (by decide) hb
  let v := decClockHOLFinite u
  have hBv : Base t0 v n S R K (enc a).length := base_dec hB
  unfold probeBody
  rw [ite_word v _ _ _ _ (eval_eq0 v lC f (by omega) hlC)]
  by_cases hf0 : f = 0
  · subst hf0
    simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [ConsLoop.assign_local v lG (.const 0) 0 1 (by simp [evalHOLExact]) hgo]
    have hans : ans = .full := by rw [← hprobe]; rfl
    obtain ⟨w, hlV⟩ := hlV
    refine Or.inr ⟨rfl, base_set hBv _ (by decide) _, 0, j, hj, by lk [v]; exact hlC, by lk [v]; exact hlJ,
      ⟨w, by lk [v]; exact hlV⟩, Or.inr ⟨by lk, by lk [v]; rw [hlRes, hans]; rfl,
        fun jj e => (by rw [hans] at e; cases e), ⟨fun _ => rfl, fun _ => hans⟩⟩⟩
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [bw, show ¬ (f' + 1 = 0) from by omega, ↓reduceIte, ne_eq, not_true_eq_false]
  -- load the slot
  obtain ⟨vs, hvs, hvs60, hsd, hsm⟩ := hmem.slot j hj
  have hsaddr := eval_slotAddr v S j (by omega) hB.s hlJ
  have hload : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (.op .add [vv lS, .shift .lsl (vv lJ) (.const 3)])) = some (.val (.word (BitVec.ofNat 64 vs))) := by
    rw [eval_load_word v _ _ hsaddr (by show u.memaddrs _; rw [hB.addrs]; exact hsd)]
    show some (ValueHOL.val (u.memory _)) = _; rw [hB.mem, hsm]
  obtain ⟨w0, hlV⟩ := hlV
  rw [seq_normal _ (ConsLoop.assign_local v lV _ _ w0 hload hlV)]
  let v1 := setVarHOLFinite lV (.val (.word (BitVec.ofNat 64 vs))) v
  have hB1 : Base t0 v1 n S R K (enc a).length := base_set hBv _ (by decide) _
  have hv1V : v1.locals.lookup lV = some (.val (.word (BitVec.ofNat 64 vs))) := lookup_setVar_same _ _ _
  rw [ite_word v1 _ _ _ _ (eval_eq0 v1 lV vs (by omega) hv1V)]
  by_cases hv0 : vs = 0
  · subst hv0
    simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [ConsLoop.assign_local v1 lG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v1, v]; exact hgo)]
    have hans : ans = .empty j := by rw [← hprobe]; simp [probeR, hvs]
    refine Or.inr ⟨rfl, base_set hB1 _ (by decide) _, f' + 1, j, hj, by lk [v1, v]; exact hlC,
      by lk [v1, v]; exact hlJ, ⟨BitVec.ofNat 64 0, by lk [v1]⟩, Or.inr ⟨by lk, by lk [v1, v]; rw [hlRes, hans]; rfl,
        fun jj e => (by rw [hans] at e; cases e; rfl), ⟨fun e => (by rw [hans] at e; cases e), fun e => by omega⟩⟩⟩
  obtain ⟨i, rfl⟩ : ∃ i, vs = i + 1 := ⟨vs - 1, by omega⟩
  simp only [bw, show ¬ (i + 1 = 0) from by omega, ↓reduceIte, ne_eq, not_true_eq_false]
  have hi := hnamed j i hvs
  obtain ⟨P, rd1, rd2, rm1, rm2, hPw⟩ := hmem.row i hi
  have hshort := hmem.short i hi
  have hraddr := eval_rowAddr v1 R i (by omega) hB1.r hv1V
  have hlen : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.load .one (.op .add [rowAddr, .const 8])) = some (.val (.word (BitVec.ofNat 64 (enc rows[i]).length))) := by
    rw [eval_load_word v1 _ (R + BitVec.ofNat 64 (16 * i) + 8)
      (by simp only [evalHOLExact, evalListHOLExact]; rw [hraddr]; simp [wordOpHOL, wordOp, valueIsWord, valueWord])
      (by show u.memaddrs _; rw [hB.addrs]; exact rd2)]
    show some (ValueHOL.val (u.memory _)) = _; rw [hB.mem, rm2]
  have hnext : rows[i] ≠ a → probeR rows slots n a (f' + 1) j = probeR rows slots n a f' ((j + 1) % n) := by
    intro hne; have : rows[i]? ≠ some a := by simp [hi]; exact hne
    simp [probeR, hvs, this]
  have go_adv : ∀ x : PanSemStateFiniteExact 64 σ, Base t0 x n S R K (enc a).length →
      x.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 (f' + 1)))) →
      x.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))) → (∃ w, x.locals.lookup lV = some (.val (.word w))) →
      x.locals.lookup lG = some (.val (.word 1)) → x.locals.lookup lRes = some (.val (.word 0)) → rows[i] ≠ a →
      Stop (evaluateHOLFiniteState x nextP).1 ∨ ((evaluateHOLFiniteState x nextP).1 = none ∧
        LInv t0 enc rows slots n S R K a ans (evaluateHOLFiniteState x nextP).2) := by
    intro x hBx c1 c2 c3 c4 c5 hne
    obtain ⟨u', e, hu'⟩ := adv t0 enc rows slots n b S R K a ans hn hb x hBx f' j hj c1 c2 c3 c4 c5
      (by rw [← hnext hne]; exact hprobe) hfn
    rw [e]; exact Or.inr ⟨rfl, hu'⟩
  have hlL : v1.locals.lookup lL = some (.val (.word (BitVec.ofNat 64 (enc a).length))) := hB1.l
  rw [ite_word v1 _ _ _ _ (ConsLoop.eval_cmp_of v1 .equal _ _ _ _ hlen (eval_vv v1 lL _ hlL))]
  by_cases hle0 : (enc rows[i]).length ≠ (enc a).length
  · have hle := hle0
    have hne' : ¬ BitVec.ofNat 64 (enc rows[i]).length = BitVec.ofNat 64 (enc a).length := fun e => hle (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (enc rows[i]).length)
        (BitVec.ofNat 64 (enc a).length) = false := by simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne']
    simp only [hc, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    exact go_adv v1 hB1 (by lk [v1, v]; exact hlC) (by lk [v1, v]; exact hlJ) ⟨_, hv1V⟩ (by lk [v1, v]; exact hgo)
      (by lk [v1, v]; exact hlRes) (fun e => hle (by rw [e]))
  have hle : (enc rows[i]).length = (enc a).length := Classical.not_not.mp hle0
  have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (BitVec.ofNat 64 (enc rows[i]).length)
      (BitVec.ofNat 64 (enc a).length) = true := by simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hle]
  simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  -- set up the comparison
  have hrow : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
      (.load .one rowAddr) = some (.val (.word P)) := by
    rw [eval_load_word v1 _ _ hraddr (by show u.memaddrs _; rw [hB.addrs]; exact rd1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [hB.mem, rm1]
  obtain ⟨wa0, ha0⟩ := hB1.cw lWa (by decide)
  rw [seq_normal _ (show evaluateHOLFiniteState v1 cmpSetup = _ from by
    unfold cmpSetup
    rw [seq_normal _ (ConsLoop.assign_local v1 lWa _ P wa0 hrow ha0)]
    have hB2 := base_set hB1 lWa (by decide) P
    obtain ⟨wb0, hb0⟩ := hB2.cw lWb (by decide)
    rw [seq_normal _ (ConsLoop.assign_local _ lWb _ K wb0 (eval_vv _ lK _ hB2.k) hb0)]
    have hB3 := base_set hB2 lWb (by decide) K
    obtain ⟨wn0, hn0⟩ := hB3.cw lWn (by decide)
    rw [seq_normal _ (ConsLoop.assign_local _ lWn _ _ wn0 (eval_vv _ lL _ hB3.l) hn0)]
    have hB4 := base_set hB3 lWn (by decide) (BitVec.ofNat 64 (enc a).length)
    obtain ⟨we0, he0⟩ := hB4.cw lWeq (by decide)
    rw [seq_normal _ (ConsLoop.assign_local _ lWeq (.const 1) 1 we0 (by simp [evalHOLExact]) he0)]
    have hB5 := base_set hB4 lWeq (by decide) 1
    obtain ⟨wg0, hg0⟩ := hB5.cw lWg (by decide)
    exact ConsLoop.assign_local _ lWg (.const 1) 1 wg0 (by simp [evalHOLExact]) hg0)]
  let v6 := setVarHOLFinite lWg (.val (.word 1)) (setVarHOLFinite lWeq (.val (.word 1))
    (setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 (enc a).length))) (setVarHOLFinite lWb (.val (.word K))
      (setVarHOLFinite lWa (.val (.word P)) v1))))
  have hB6 : Base t0 v6 n S R K (enc a).length :=
    base_set (base_set (base_set (base_set (base_set hB1 _ (by decide) _) _ (by decide) _) _ (by decide) _) _
      (by decide) _) _ (by decide) _
  have hW1 : Words v6 P (enc rows[i]) := fun k hk => by
    rw [show v6.memaddrs = t0.memaddrs from hB6.addrs, show v6.memory = t0.memory from hB6.mem]; exact hPw k hk
  have hW2 : Words v6 K (enc a) := fun k hk => by
    rw [show v6.memaddrs = t0.memaddrs from hB6.addrs, show v6.memory = t0.memory from hB6.mem]; exact hK k hk
  rcases cmpLoop_spec v6 P K (enc rows[i]) (enc a) hle (by omega) hW1 hW2 (by lk [v6]) (by lk [v6])
      (by lk [v6]; rw [hle]) (by lk [v6]) (by lk [v6]) with hs | ⟨hn6, hCI, hweq⟩
  · exact Or.inl (seq_stop _ _ _ hs)
  generalize hw : evaluateHOLFiniteState v6 cmpLoop = wst at hn6 hCI hweq
  obtain ⟨w1, w⟩ := wst
  simp only at hn6 hCI hweq; subst hn6
  rw [seq_normal _ hw]
  obtain ⟨cm, cd, cc, cg, ct, cfr, k, _, cla, clb, cln, _, cbr⟩ := hCI
  have cgw : ∃ z, w.locals.lookup lWg = some (.val (.word z)) := by
    rcases cbr with ⟨h, _⟩ | ⟨h, _⟩ <;> exact ⟨_, h⟩
  have hBw : Base t0 w n S R K (enc a).length := by
    refine ⟨by rw [cm]; exact hB6.mem, by rw [cd]; exact hB6.addrs, by rw [cc]; exact hB6.code,
      by rw [cg]; exact hB6.globals, by rw [ct]; exact hB6.top, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [cfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB6.s
    · rw [cfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB6.r
    · rw [cfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB6.m
    · rw [cfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB6.k
    · rw [cfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hB6.l
    · simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨_, _, _, _, _, a1, a2, a3, a4, a5⟩ := hy
      rw [cfr y a1 a2 a3 a4 a5]; exact hB6.fr y (by simp [scr]; exact ⟨by assumption, by assumption, by assumption,
        by assumption, by assumption, a1, a2, a3, a4, a5⟩)
    · simp only [cscr, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, cla⟩
      · exact ⟨_, clb⟩
      · exact ⟨_, cln⟩
      · exact ⟨_, hweq⟩
      · exact cgw
  have keep : ∀ y, y ∉ cscr → w.locals.lookup y = v6.locals.lookup y := by
    intro y hy; simp only [cscr, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact cfr y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
  have wC : w.locals.lookup lC = some (.val (.word (BitVec.ofNat 64 (f' + 1)))) := by
    rw [keep _ (by decide)]; lk [v6, v1, v]; exact hlC
  have wJ : w.locals.lookup lJ = some (.val (.word (BitVec.ofNat 64 j))) := by
    rw [keep _ (by decide)]; lk [v6, v1, v]; exact hlJ
  have wV : w.locals.lookup lV = some (.val (.word (BitVec.ofNat 64 (i + 1)))) := by
    rw [keep _ (by decide)]; lk [v6, v1]
  have wG : w.locals.lookup lG = some (.val (.word 1)) := by rw [keep _ (by decide)]; lk [v6, v1, v]; exact hgo
  have wR : w.locals.lookup lRes = some (.val (.word 0)) := by rw [keep _ (by decide)]; lk [v6, v1, v]; exact hlRes
  rw [ite_word w _ _ _ _ (eval_vv w lWeq _ hweq)]
  by_cases he : enc rows[i] = enc a
  · simp only [bw, he, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have heq : rows[i] = a := hinj _ _ he
    have hans : ans = .hit i := by rw [← hprobe]; simp [probeR, hvs, hi, heq]
    rw [seq_normal _ (ConsLoop.assign_local w lRes (vv lV) (BitVec.ofNat 64 (i + 1)) 0 (eval_vv w lV _ wV) wR)]
    rw [ConsLoop.assign_local _ lG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk; exact wG)]
    exact Or.inr ⟨rfl, base_set (base_set hBw _ (by decide) _) _ (by decide) _, f' + 1, j, hj, by lk; exact wC,
      by lk; exact wJ, ⟨_, by lk; exact wV⟩, Or.inr ⟨by lk, by lk; rw [hans]; rfl,
        fun jj e => (by rw [hans] at e; cases e), ⟨fun e => (by rw [hans] at e; cases e), fun e => by omega⟩⟩⟩
  · simp only [bw, he, ↓reduceIte, ne_eq, not_true_eq_false]
    exact go_adv w hBw wC wJ ⟨_, wV⟩ wG wR (fun e => he (by rw [e]))

end

section
variable {σ : Type} {α : Type} [DecidableEq α]

theorem probeLoop_spec (t0 : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (rows : List α)
    (slots : List Nat) (n b : Nat) (S R K : BitVec 64) (a : α) (ans : PR)
    (hn : n = 2 ^ b) (hb : b ≤ 60) (hmem : VMem t0 enc rows slots n S R) (hK : Words t0 K (enc a))
    (hKl : (enc a).length < 2 ^ 61)
    (hnamed : ∀ (j i : Nat), slots[j]? = some (i + 1) → i < rows.length) (hinj : ∀ x y, enc x = enc y → x = y)
    (u0 : PanSemStateFiniteExact 64 σ) (hI : LInv t0 enc rows slots n S R K a ans u0) :
    Stop (evaluateHOLFiniteState u0 probeLoop).1 ∨ ((evaluateHOLFiniteState u0 probeLoop).1 = none ∧
      LInv t0 enc rows slots n S R K a ans (evaluateHOLFiniteState u0 probeLoop).2 ∧
      (evaluateHOLFiniteState u0 probeLoop).2.locals.lookup lG = some (.val (.word 0))) := by
  have := while_stop (vv lG) probeBody (LInv t0 enc rows slots n S R K a ans)
    (fun u => LInv t0 enc rows slots n S R K a ans u ∧ u.locals.lookup lG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, f, j, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hgo, _⟩ | ⟨hg0, _⟩
      · exact ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hgo], fun h => absurd h (by decide),
          fun _ _ => probe_step t0 enc rows slots n b S R K a ans hn hb hmem hK hKl hnamed hinj u hu hgo⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg0], fun _ => ⟨hu, hg0⟩, fun h => absurd rfl h⟩)
    u0 hI
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end

end ConPanqueque.V
