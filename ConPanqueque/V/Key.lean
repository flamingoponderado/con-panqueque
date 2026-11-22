import ConPanqueque.ConsLoop
import ConPanqueque.Logic.Stop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic

/-!
# Word sequences in memory, and comparing two of them

The generic cons tables key rows by word sequences (`List (BitVec 64)`), so that
records with strings, unbounded numbers or lists can be hash-consed like
fixed-width ones. `Words t A xs`: the words `xs` at `A, A+8, …`. `cmpLoop`
compares `len` words at `wa` with `len` words at `wb` and leaves `weq` = 1 iff
they agree. Specs here are "stop, or correct", with no clock premises.
-/

namespace ConPanqueque.V

def vv (n : MlS) : ExpHOL 64 := .var .local n

def lWa := ofString "wa"
def lWb := ofString "wb"
def lWn := ofString "wn"
def lWeq := ofString "weq"
def lWg := ofString "wg"

/-- The words `xs` stored at `A, A + 8, …`. -/
def Words {σ : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (xs : List (BitVec 64)) : Prop :=
  ∀ k (hk : k < xs.length), t.memaddrs (A + BitVec.ofNat 64 (8 * k)) ∧
    t.memory (A + BitVec.ofNat 64 (8 * k)) = .word xs[k]

theorem lookup_decClock {σ : Type} (u : PanSemStateFiniteExact 64 σ) (y : MlS) :
    (decClockHOLFinite u).locals.lookup y = u.locals.lookup y := rfl

/-- Local lookups through `setVar`s and clock ticks, distinct names decided. -/
syntax "lk" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lk) => `(tactic| simp (disch := first | decide | assumption) only [lookup_setVar_other, lookup_setVar_same, lookup_decClock])
  | `(tactic| lk [$ls,*]) =>
    `(tactic| simp (disch := first | decide | assumption) only [$ls,*, lookup_setVar_other, lookup_setVar_same, lookup_decClock])

theorem eval_vv {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (val : ValueHOL 64)
    (h : s.locals.lookup x = some val) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (vv x) = some val := by
  simp [vv, evalHOLExact, h]

theorem eval_add_c {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (w c : BitVec 64)
    (h : s.locals.lookup x = some (.val (.word w))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op .add [vv x, .const c]) =
      some (.val (.word (w + c))) := by
  simp [vv, evalHOLExact, evalListHOLExact, h, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem eval_sub_c {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (w c : BitVec 64)
    (h : s.locals.lookup x = some (.val (.word w))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op .sub [vv x, .const c]) =
      some (.val (.word (w - c))) := by
  simp [vv, evalHOLExact, evalListHOLExact, h, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem addr_succ (A : BitVec 64) (k : Nat) :
    A + BitVec.ofNat 64 (8 * k) + 8 = A + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

def cmpBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv lWn) (.const 0)) (.assign .local lWg (.const 0))
   (.ite (.cmp .equal (.load .one (vv lWa)) (.load .one (vv lWb)))
     (.seq (.assign .local lWa (.op .add [vv lWa, .const 8]))
      (.seq (.assign .local lWb (.op .add [vv lWb, .const 8]))
        (.assign .local lWn (.op .sub [vv lWn, .const 1]))))
     (.seq (.assign .local lWeq (.const 0)) (.assign .local lWg (.const 0))))

def cmpLoop : ProgHOL 64 := .while (vv lWg) cmpBody

def bw (b : Prop) [Decidable b] : BitVec 64 := if b then 1 else 0

/-- The comparison loop's invariant: `k` words agree so far. -/
def CI {σ : Type} (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs ys : List (BitVec 64))
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lWa → y ≠ lWb → y ≠ lWn → y ≠ lWeq → y ≠ lWg → u.locals.lookup y = t.locals.lookup y) ∧
  ∃ k, k ≤ xs.length ∧ u.locals.lookup lWa = some (.val (.word (A + BitVec.ofNat 64 (8 * k)))) ∧
    u.locals.lookup lWb = some (.val (.word (B + BitVec.ofNat 64 (8 * k)))) ∧
    u.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) ∧
    xs.take k = ys.take k ∧
    ((u.locals.lookup lWg = some (.val (.word 1)) ∧ u.locals.lookup lWeq = some (.val (.word 1))) ∨
     (u.locals.lookup lWg = some (.val (.word 0)) ∧ u.locals.lookup lWeq = some (.val (.word (bw (xs = ys))))))

section
variable {σ : Type}

theorem cmp_step (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs ys : List (BitVec 64))
    (hlen : xs.length = ys.length) (hL : xs.length < 2 ^ 64) (hA : Words t A xs) (hB : Words t B ys)
    (u : PanSemStateFiniteExact 64 σ) (hu : CI t A B xs ys u) (hg : u.locals.lookup lWg = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) cmpBody = (none, u') ∧ CI t A B xs ys u' := by
  obtain ⟨m0, d0, c0, g0, ta0, fr, k, hk, la, lb, ln, htk, br⟩ := hu
  obtain ⟨_, leq⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  let v := decClockHOLFinite u
  have hn0 : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.cmp .equal (vv lWn) (.const 0)) = some (.val (.word (bw (xs.length - k = 0)))) := by
    rw [ConsLoop.eval_cmp_of v .equal _ _ (BitVec.ofNat 64 (xs.length - k)) 0 (eval_vv v lWn _ ln)
      (by simp [evalHOLExact])]
    simp only [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : xs.length - k = 0
    · simp [h]
    · have : ¬ BitVec.ofNat 64 (xs.length - k) = 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp only [h, decide_false, ↓reduceIte, beq_iff_eq, this]
  unfold cmpBody
  rw [ite_word v _ _ _ _ hn0]
  by_cases hkl : xs.length - k = 0
  · simp only [bw, hkl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [ConsLoop.assign_local v lWg (.const 0) 0 1 (by simp [evalHOLExact]) hg]
    have hk' : k = xs.length := by omega
    have heq : xs = ys := by
      have := htk; rw [hk', List.take_length, hlen, List.take_length] at this; exact this
    refine ⟨setVarHOLFinite lWg (.val (.word 0)) v, rfl, m0, d0, c0, g0, ta0,
      fun y a1 a2 a3 a4 a5 => by lk [v]; exact fr y a1 a2 a3 a4 a5, k, hk,
      by lk [v]; exact la, by lk [v]; exact lb, by lk [v]; exact ln, htk,
      Or.inr ⟨by lk [v], by lk [v]; rw [leq]; simp [bw, heq]⟩⟩
  simp only [bw, hkl, ↓reduceIte, ne_eq, not_true_eq_false]
  have hkx : k < xs.length := by omega
  have hky : k < ys.length := by omega
  have hx : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (vv lWa)) = some (.val (.word xs[k])) := by
    rw [eval_load_word v _ _ (eval_vv v lWa _ la)
      (by show u.memaddrs _; rw [d0]; exact (hA k hkx).1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, (hA k hkx).2]
  have hy : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (vv lWb)) = some (.val (.word ys[k])) := by
    rw [eval_load_word v _ _ (eval_vv v lWb _ lb)
      (by show u.memaddrs _; rw [d0]; exact (hB k hky).1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, (hB k hky).2]
  rw [ite_word v _ _ _ _ (ConsLoop.eval_cmp_of v .equal _ _ _ _ hx hy)]
  by_cases hxy : xs[k] = ys[k]
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal xs[k] ys[k] = true := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hxy]
    simp only [hc, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [seq_normal _ (ConsLoop.assign_local v lWa _ (A + BitVec.ofNat 64 (8 * (k + 1))) _
      (by rw [eval_add_c v lWa _ _ la, addr_succ]) la)]
    let v1 := setVarHOLFinite lWa (.val (.word (A + BitVec.ofNat 64 (8 * (k + 1))))) v
    have lb1 : v1.locals.lookup lWb = some (.val (.word (B + BitVec.ofNat 64 (8 * k)))) := by lk [v1, v]; exact lb
    rw [seq_normal _ (ConsLoop.assign_local v1 lWb _ (B + BitVec.ofNat 64 (8 * (k + 1))) _
      (by rw [eval_add_c v1 lWb _ _ lb1, addr_succ]) lb1)]
    let v2 := setVarHOLFinite lWb (.val (.word (B + BitVec.ofNat 64 (8 * (k + 1))))) v1
    have ln2 : v2.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) := by
      lk [v2, v1, v]; exact ln
    rw [ConsLoop.assign_local v2 lWn _ (BitVec.ofNat 64 (xs.length - (k + 1))) _
      (by rw [eval_sub_c v2 lWn _ _ ln2]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ln2]
    refine ⟨setVarHOLFinite lWn (.val (.word (BitVec.ofNat 64 (xs.length - (k + 1))))) v2, rfl, m0, d0, c0, g0, ta0,
      fun y a1 a2 a3 a4 a5 => by lk [v2, v1, v]; exact fr y a1 a2 a3 a4 a5,
      k + 1, hkx, by lk [v2, v1, v], by lk [v2, v1, v], by lk [v2, v1, v], ?_,
      Or.inl ⟨by lk [v2, v1, v]; exact hg, by lk [v2, v1, v]; exact leq⟩⟩
    rw [List.take_add_one, List.take_add_one, htk, List.getElem?_eq_getElem hkx, List.getElem?_eq_getElem hky, hxy]
  · have hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal xs[k] ys[k] = false := by
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hxy]
    simp only [hc, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    rw [seq_normal _ (ConsLoop.assign_local v lWeq (.const 0) 0 1 (by simp [evalHOLExact]) leq)]
    let v1 := setVarHOLFinite lWeq (.val (.word 0)) v
    rw [ConsLoop.assign_local v1 lWg (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [v1, v]; exact hg)]
    have hne : xs ≠ ys := fun e => hxy (by subst e; rfl)
    refine ⟨setVarHOLFinite lWg (.val (.word 0)) v1, rfl, m0, d0, c0, g0, ta0,
      fun y a1 a2 a3 a4 a5 => by lk [v1, v]; exact fr y a1 a2 a3 a4 a5,
      k, hk, by lk [v1, v]; exact la, by lk [v1, v]; exact lb, by lk [v1, v]; exact ln, htk,
      Or.inr ⟨by lk [v1, v], by lk [v1, v]; simp [bw, hne]⟩⟩

theorem cmpLoop_spec (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs ys : List (BitVec 64))
    (hlen : xs.length = ys.length) (hL : xs.length < 2 ^ 64) (hA : Words t A xs) (hB : Words t B ys)
    (la : t.locals.lookup lWa = some (.val (.word A))) (lb : t.locals.lookup lWb = some (.val (.word B)))
    (ln : t.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 xs.length))))
    (leq : t.locals.lookup lWeq = some (.val (.word 1))) (lg : t.locals.lookup lWg = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState t cmpLoop).1 ∨ ((evaluateHOLFiniteState t cmpLoop).1 = none ∧
      CI t A B xs ys (evaluateHOLFiniteState t cmpLoop).2 ∧
      (evaluateHOLFiniteState t cmpLoop).2.locals.lookup lWeq = some (.val (.word (bw (xs = ys))))) := by
  have := while_stop (vv lWg) cmpBody (CI t A B xs ys)
    (fun u => CI t A B xs ys u ∧ u.locals.lookup lWeq = some (.val (.word (bw (xs = ys)))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, k, _, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, heq⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := cmp_step t A B xs ys hlen hL hA hB u hu hg
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, heq⟩, fun h => absurd rfl h⟩)
    t ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl, 0, Nat.zero_le _, by simpa using la, by simpa using lb,
      by simpa using ln, by simp, Or.inl ⟨lg, leq⟩⟩
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩
end

/-! ## Hashing a word sequence

`hashLoop` folds `h ↦ h·M + w` over the `wn` words at `wa` into `wh`. Any
function would do for correctness; this one is the model's `hashW`. -/

def lWh := ofString "wh"
def hM : BitVec 64 := 0x9e3779b97f4a7c15#64

def hashW (xs : List (BitVec 64)) : BitVec 64 := xs.foldl (fun h w => h * hM + w) 0

theorem eval_muladd {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (w c y : BitVec 64)
    (h : s.locals.lookup x = some (.val (.word w)))
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word y))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.panop .mul [vv x, .const c], e]) = some (.val (.word (w * c + y))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, evalHOLExact, vv, h, he, panOpHOL, wordOpHOL, wordOp, valueIsWord,
    valueWord]

def hashBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv lWn) (.const 0)) (.assign .local lWg (.const 0))
   (.seq (.assign .local lWh (.op .add [.panop .mul [vv lWh, .const hM], .load .one (vv lWa)]))
    (.seq (.assign .local lWa (.op .add [vv lWa, .const 8]))
      (.assign .local lWn (.op .sub [vv lWn, .const 1]))))

def hashLoop : ProgHOL 64 := .while (vv lWg) hashBody

def HI {σ : Type} (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (xs : List (BitVec 64))
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lWa → y ≠ lWn → y ≠ lWh → y ≠ lWg → u.locals.lookup y = t.locals.lookup y) ∧
  ∃ k, k ≤ xs.length ∧ u.locals.lookup lWa = some (.val (.word (A + BitVec.ofNat 64 (8 * k)))) ∧
    u.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) ∧
    ((u.locals.lookup lWg = some (.val (.word 1)) ∧
        u.locals.lookup lWh = some (.val (.word (hashW (xs.take k))))) ∨
     (u.locals.lookup lWg = some (.val (.word 0)) ∧ u.locals.lookup lWh = some (.val (.word (hashW xs)))))

section
variable {σ : Type}

theorem hash_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (xs : List (BitVec 64))
    (hL : xs.length < 2 ^ 64) (hA : Words t A xs)
    (u : PanSemStateFiniteExact 64 σ) (hu : HI t A xs u) (hg : u.locals.lookup lWg = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) hashBody = (none, u') ∧ HI t A xs u' := by
  obtain ⟨m0, d0, c0, g0, ta0, fr, k, hk, la, ln, br⟩ := hu
  obtain ⟨_, lh⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  let v := decClockHOLFinite u
  have hn0 : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.cmp .equal (vv lWn) (.const 0)) = some (.val (.word (bw (xs.length - k = 0)))) := by
    rw [ConsLoop.eval_cmp_of v .equal _ _ (BitVec.ofNat 64 (xs.length - k)) 0 (eval_vv v lWn _ ln)
      (by simp [evalHOLExact])]
    simp only [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : xs.length - k = 0
    · simp [h]
    · have : ¬ BitVec.ofNat 64 (xs.length - k) = 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp only [h, decide_false, ↓reduceIte, beq_iff_eq, this]
  unfold hashBody
  rw [ite_word v _ _ _ _ hn0]
  by_cases hkl : xs.length - k = 0
  · simp only [bw, hkl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [ConsLoop.assign_local v lWg (.const 0) 0 1 (by simp [evalHOLExact]) hg]
    have hk' : k = xs.length := by omega
    refine ⟨setVarHOLFinite lWg (.val (.word 0)) v, rfl, m0, d0, c0, g0, ta0,
      fun y a1 a2 a3 a4 => by lk [v]; exact fr y a1 a2 a3 a4, k, hk,
      by lk [v]; exact la, by lk [v]; exact ln, Or.inr ⟨by lk [v], by lk [v]; rw [lh, hk', List.take_length]⟩⟩
  simp only [bw, hkl, ↓reduceIte, ne_eq, not_true_eq_false]
  have hkx : k < xs.length := by omega
  have hx : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (vv lWa)) = some (.val (.word xs[k])) := by
    rw [eval_load_word v _ _ (eval_vv v lWa _ la) (by show u.memaddrs _; rw [d0]; exact (hA k hkx).1)]
    show some (ValueHOL.val (u.memory _)) = _; rw [m0, (hA k hkx).2]
  have hh : hashW (xs.take (k + 1)) = hashW (xs.take k) * hM + xs[k] := by
    unfold hashW; rw [List.take_add_one, List.getElem?_eq_getElem hkx, Option.toList_some, List.foldl_append]; rfl
  rw [seq_normal _ (ConsLoop.assign_local v lWh _ (hashW (xs.take (k + 1))) _
    (by rw [hh]; exact eval_muladd v lWh _ _ _ _ lh hx) lh)]
  let v1 := setVarHOLFinite lWh (.val (.word (hashW (xs.take (k + 1))))) v
  have la1 : v1.locals.lookup lWa = some (.val (.word (A + BitVec.ofNat 64 (8 * k)))) := by lk [v1, v]; exact la
  rw [seq_normal _ (ConsLoop.assign_local v1 lWa _ (A + BitVec.ofNat 64 (8 * (k + 1))) _
    (by rw [eval_add_c v1 lWa _ _ la1, addr_succ]) la1)]
  let v2 := setVarHOLFinite lWa (.val (.word (A + BitVec.ofNat 64 (8 * (k + 1))))) v1
  have ln2 : v2.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) := by
    lk [v2, v1, v]; exact ln
  rw [ConsLoop.assign_local v2 lWn _ (BitVec.ofNat 64 (xs.length - (k + 1))) _
    (by rw [eval_sub_c v2 lWn _ _ ln2]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ln2]
  exact ⟨_, rfl, m0, d0, c0, g0, ta0, fun y a1 a2 a3 a4 => by lk [v2, v1, v]; exact fr y a1 a2 a3 a4,
    k + 1, hkx, by lk [v2, v1, v], by lk [v2, v1, v], Or.inl ⟨by lk [v2, v1, v]; exact hg, by lk [v2, v1, v]⟩⟩

theorem hashLoop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (xs : List (BitVec 64))
    (hL : xs.length < 2 ^ 64) (hA : Words t A xs)
    (la : t.locals.lookup lWa = some (.val (.word A)))
    (ln : t.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 xs.length))))
    (lh : t.locals.lookup lWh = some (.val (.word 0))) (lg : t.locals.lookup lWg = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState t hashLoop).1 ∨ ((evaluateHOLFiniteState t hashLoop).1 = none ∧
      HI t A xs (evaluateHOLFiniteState t hashLoop).2 ∧
      (evaluateHOLFiniteState t hashLoop).2.locals.lookup lWh = some (.val (.word (hashW xs)))) := by
  have := while_stop (vv lWg) hashBody (HI t A xs)
    (fun u => HI t A xs u ∧ u.locals.lookup lWh = some (.val (.word (hashW xs))))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, k, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, hh⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := hash_step t A xs hL hA u hu hg
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hh⟩, fun h => absurd rfl h⟩)
    t ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, 0, Nat.zero_le _, by simpa using la,
      by simpa using ln, Or.inl ⟨lg, by simpa [hashW] using lh⟩⟩
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩
end

/-! ## Copying a word sequence

`copyLoop` copies the `wn` words at `wa` to `wb`. The memory afterwards is
`wr m B xs`: `m` with `xs` written at `B, B+8, …`. -/

def upd (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

def wr (m : BitVec 64 → HolWordLab 64) (B : BitVec 64) : List (BitVec 64) → (BitVec 64 → HolWordLab 64)
  | [] => m
  | y :: ys => wr (upd m B y) (B + 8) ys

theorem addr_shift (B : BitVec 64) (j : Nat) : B + 8 + BitVec.ofNat 64 (8 * j) = B + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem wr_snoc (m : BitVec 64 → HolWordLab 64) (B : BitVec 64) (ys : List (BitVec 64)) (y : BitVec 64) :
    wr m B (ys ++ [y]) = upd (wr m B ys) (B + BitVec.ofNat 64 (8 * ys.length)) y := by
  induction ys generalizing m B with
  | nil => simp [wr]
  | cons z zs ih => simp only [List.cons_append, wr, List.length_cons]; rw [ih, addr_shift]

theorem wr_out (m : BitVec 64 → HolWordLab 64) (B : BitVec 64) (ys : List (BitVec 64)) (c : BitVec 64)
    (hc : ∀ j, j < ys.length → c ≠ B + BitVec.ofNat 64 (8 * j)) : wr m B ys c = m c := by
  induction ys generalizing m B with
  | nil => rfl
  | cons z zs ih =>
    simp only [wr]
    rw [ih _ _ (fun j hj => by rw [addr_shift]; exact hc (j + 1) (by simp; omega))]
    simp only [upd]; rw [if_neg (by simpa using hc 0 (by simp))]

theorem addr_inj (B : BitVec 64) (i j : Nat) (hi : i < 2 ^ 61) (hj : j < 2 ^ 61)
    (h : B + BitVec.ofNat 64 (8 * i) = B + BitVec.ofNat 64 (8 * j)) : i = j := by
  have h2 := (BitVec.add_right_inj B).mp h
  have := congrArg BitVec.toNat h2
  simp at this; omega

theorem wr_at (m : BitVec 64 → HolWordLab 64) (B : BitVec 64) (ys : List (BitVec 64)) (hl : ys.length < 2 ^ 61)
    (k : Nat) (hk : k < ys.length) : wr m B ys (B + BitVec.ofNat 64 (8 * k)) = .word ys[k] := by
  have e : ys = ys.take k ++ [ys[k]] ++ ys.drop (k + 1) := by simp
  generalize hzs : ys.drop (k + 1) = zs at e
  have hzl : zs.length = ys.length - (k + 1) := by rw [← hzs]; simp
  have e2 : wr m B ys (B + BitVec.ofNat 64 (8 * k)) =
      wr m B (ys.take k ++ [ys[k]] ++ zs) (B + BitVec.ofNat 64 (8 * k)) := by rw [← e]
  rw [e2]
  -- the words after `k` are written at addresses other than `B + 8k`
  have hlen : (ys.take k ++ [ys[k]]).length = k + 1 := by simp; omega
  have gen : ∀ (zs : List (BitVec 64)) (pre : List (BitVec 64)),
      k + 1 ≤ pre.length → pre.length + zs.length < 2 ^ 61 →
      wr m B (pre ++ zs) (B + BitVec.ofNat 64 (8 * k)) = wr m B pre (B + BitVec.ofNat 64 (8 * k)) := by
    intro zs
    induction zs with
    | nil => intros; simp
    | cons z zs ih =>
      intro pre hp hl'
      rw [show pre ++ z :: zs = (pre ++ [z]) ++ zs by simp, ih (pre ++ [z]) (by simp; omega) (by simp at hl' ⊢; omega),
        wr_snoc, upd, if_neg]
      intro h; have := addr_inj B _ _ (by omega) (by simp at hl'; omega) h; omega
  rw [gen zs _ (by rw [hlen]; exact Nat.le_refl _) (by rw [hlen]; omega), wr_snoc, upd,
    if_pos (by rw [show (ys.take k).length = k by simp; omega])]

def copyBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv lWn) (.const 0)) (.assign .local lWg (.const 0))
   (.seq (.store (vv lWb) (.load .one (vv lWa)))
    (.seq (.assign .local lWa (.op .add [vv lWa, .const 8]))
     (.seq (.assign .local lWb (.op .add [vv lWb, .const 8]))
       (.assign .local lWn (.op .sub [vv lWn, .const 1])))))

def copyLoop : ProgHOL 64 := .while (vv lWg) copyBody

def CpI {σ : Type} (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs : List (BitVec 64))
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧ u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lWa → y ≠ lWb → y ≠ lWn → y ≠ lWg → u.locals.lookup y = t.locals.lookup y) ∧
  ∃ k, k ≤ xs.length ∧ u.memory = wr t.memory B (xs.take k) ∧
    u.locals.lookup lWa = some (.val (.word (A + BitVec.ofNat 64 (8 * k)))) ∧
    u.locals.lookup lWb = some (.val (.word (B + BitVec.ofNat 64 (8 * k)))) ∧
    u.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) ∧
    (u.locals.lookup lWg = some (.val (.word 1)) ∨ (u.locals.lookup lWg = some (.val (.word 0)) ∧ k = xs.length))

section
variable {σ : Type}

theorem copy_step (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs : List (BitVec 64))
    (hL : xs.length < 2 ^ 61) (hA : Words t A xs) (hB : ∀ k, k < xs.length → t.memaddrs (B + BitVec.ofNat 64 (8 * k)))
    (hdis : ∀ i j, i < xs.length → j < xs.length → A + BitVec.ofNat 64 (8 * i) ≠ B + BitVec.ofNat 64 (8 * j))
    (u : PanSemStateFiniteExact 64 σ) (hu : CpI t A B xs u) (hg : u.locals.lookup lWg = some (.val (.word 1))) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) copyBody = (none, u') ∧ CpI t A B xs u' := by
  obtain ⟨d0, c0, g0, ta0, fr, k, hk, m0, la, lb, ln, _⟩ := hu
  let v := decClockHOLFinite u
  have hn0 : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.cmp .equal (vv lWn) (.const 0)) = some (.val (.word (bw (xs.length - k = 0)))) := by
    rw [ConsLoop.eval_cmp_of v .equal _ _ (BitVec.ofNat 64 (xs.length - k)) 0 (eval_vv v lWn _ ln)
      (by simp [evalHOLExact])]
    simp only [bw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases h : xs.length - k = 0
    · simp [h]
    · have : ¬ BitVec.ofNat 64 (xs.length - k) = 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp only [h, ↓reduceIte, beq_iff_eq, this]
  unfold copyBody
  rw [ite_word v _ _ _ _ hn0]
  by_cases hkl : xs.length - k = 0
  · simp only [bw, hkl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [ConsLoop.assign_local v lWg (.const 0) 0 1 (by simp [evalHOLExact]) hg]
    exact ⟨setVarHOLFinite lWg (.val (.word 0)) v, rfl, d0, c0, g0, ta0,
      fun y a1 a2 a3 a4 => by lk [v]; exact fr y a1 a2 a3 a4, k, hk, m0,
      by lk [v]; exact la, by lk [v]; exact lb, by lk [v]; exact ln, Or.inr ⟨by lk [v], by omega⟩⟩
  simp only [bw, hkl, ↓reduceIte, ne_eq, not_true_eq_false]
  have hkx : k < xs.length := by omega
  have hx : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
      (.load .one (vv lWa)) = some (.val (.word xs[k])) := by
    rw [eval_load_word v _ _ (eval_vv v lWa _ la) (by show u.memaddrs _; rw [d0]; exact (hA k hkx).1)]
    show some (ValueHOL.val (u.memory _)) = _
    rw [m0, wr_out _ _ _ _ (fun j hj => hdis k j hkx (by simp at hj; omega)), (hA k hkx).2]
  rw [seq_normal _ (store_word v (vv lWb) _ _ _ (eval_vv v lWb _ lb) hx
    (by show u.memaddrs _; rw [d0]; exact hB k hkx))]
  let v1 : PanSemStateFiniteExact 64 σ :=
    { v with memory := fun c => if c = B + BitVec.ofNat 64 (8 * k) then .word xs[k] else v.memory c }
  have la1 : v1.locals.lookup lWa = some (.val (.word (A + BitVec.ofNat 64 (8 * k)))) := la
  rw [seq_normal _ (ConsLoop.assign_local v1 lWa _ (A + BitVec.ofNat 64 (8 * (k + 1))) _
    (by rw [eval_add_c v1 lWa _ _ la1, addr_succ]) la1)]
  let v2 := setVarHOLFinite lWa (.val (.word (A + BitVec.ofNat 64 (8 * (k + 1))))) v1
  have lb2 : v2.locals.lookup lWb = some (.val (.word (B + BitVec.ofNat 64 (8 * k)))) := by lk [v2]; exact lb
  rw [seq_normal _ (ConsLoop.assign_local v2 lWb _ (B + BitVec.ofNat 64 (8 * (k + 1))) _
    (by rw [eval_add_c v2 lWb _ _ lb2, addr_succ]) lb2)]
  let v3 := setVarHOLFinite lWb (.val (.word (B + BitVec.ofNat 64 (8 * (k + 1))))) v2
  have ln3 : v3.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 (xs.length - k)))) := by
    lk [v3, v2]; exact ln
  rw [ConsLoop.assign_local v3 lWn _ (BitVec.ofNat 64 (xs.length - (k + 1))) _
    (by rw [eval_sub_c v3 lWn _ _ ln3]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ln3]
  refine ⟨_, rfl, d0, c0, g0, ta0, fun y a1 a2 a3 a4 => by lk [v3, v2]; exact fr y a1 a2 a3 a4,
    k + 1, hkx, ?_, by lk [v3, v2], by lk [v3, v2], by lk [v3, v2], Or.inl (by lk [v3, v2]; exact hg)⟩
  show (fun c => if c = B + BitVec.ofNat 64 (8 * k) then .word xs[k] else u.memory c) = _
  rw [List.take_add_one, List.getElem?_eq_getElem hkx, Option.toList_some, wr_snoc, m0]
  have : (xs.take k).length = k := by simp; omega
  rw [this]; rfl

/-- After the copy: memory is `wr t.memory B xs`, so `B` holds `xs`. -/
theorem copyLoop_spec (t : PanSemStateFiniteExact 64 σ) (A B : BitVec 64) (xs : List (BitVec 64))
    (hL : xs.length < 2 ^ 61) (hA : Words t A xs) (hB : ∀ k, k < xs.length → t.memaddrs (B + BitVec.ofNat 64 (8 * k)))
    (hdis : ∀ i j, i < xs.length → j < xs.length → A + BitVec.ofNat 64 (8 * i) ≠ B + BitVec.ofNat 64 (8 * j))
    (la : t.locals.lookup lWa = some (.val (.word A))) (lb : t.locals.lookup lWb = some (.val (.word B)))
    (ln : t.locals.lookup lWn = some (.val (.word (BitVec.ofNat 64 xs.length))))
    (lg : t.locals.lookup lWg = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState t copyLoop).1 ∨ ((evaluateHOLFiniteState t copyLoop).1 = none ∧
      CpI t A B xs (evaluateHOLFiniteState t copyLoop).2 ∧
      (evaluateHOLFiniteState t copyLoop).2.memory = wr t.memory B xs) := by
  have := while_stop (vv lWg) copyBody (CpI t A B xs)
    (fun u => CpI t A B xs u ∧ u.memory = wr t.memory B xs)
    (fun u hu => by
      obtain ⟨_, _, _, _, _, k, _, hm, _, _, _, br⟩ := id hu
      rcases br with hg | ⟨hg, hk⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        obtain ⟨u', e, hu'⟩ := copy_step t A B xs hL hA hB hdis u hu hg
        rw [e]; exact Or.inr ⟨rfl, hu'⟩
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg],
          fun _ => ⟨hu, by rw [hm, hk, List.take_length]⟩, fun h => absurd rfl h⟩)
    t ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, 0, Nat.zero_le _, by simp [wr], by simpa using la,
      by simpa using lb, by simpa using ln, Or.inl lg⟩
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩
end

end ConPanqueque.V
