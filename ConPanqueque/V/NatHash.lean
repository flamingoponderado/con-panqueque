import ConPanqueque.V.StrHash
import ConPanqueque.V.Enc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Hash

/-!
# A `Nat` literal's hash in Pancake

con-leche's `natHash n` is `n` below `2^64` and its vendored `natBigHash`
above; both are `leanNatHash` over the number's 64-bit words (under the
runtime assumption for the big case). `natHashP` folds the words (held as
`Enc.limbs`, `nn` of them at `na`) from the least significant.
-/

namespace ConPanqueque.V

theorem natWords_limbs (n : Nat) : (natWords n).map UInt64.toBitVec = Enc.limbs n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold natWords Enc.limbs
    by_cases h : n = 0
    · subst h; rfl
    · simp only [h, ↓reduceDIte, List.map_cons]
      rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]
      congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem natHash_eq (ra : RuntimeAssumptions) (n : Nat) : ConLeche.natHash n = leanNatHash n := by
  unfold ConLeche.natHash
  split
  · rename_i h
    unfold leanNatHash natWords
    by_cases h0 : n = 0
    · subst h0; rfl
    · have : n / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by simpa [ConLeche.natHashWordBound] using h)
      simp only [h0, ↓reduceDIte, this]
      rw [natWords]; simp
  · rename_i h
    exact ra.natBigHash n (by simpa [ConLeche.natHashWordBound] using h)

def lNa := ofString "na"
def lNn := ofString "nn"
def lNh := ofString "nh"
def lNi := ofString "ni"

/-- `nh := 0` for no words, else `w0` mixed with the rest in order. -/
def natHashP : ProgHOL 64 :=
  .ite (vv lNn)
    (.seq (.assign .local lNh (.load .one (vv lNa)))
     (.seq (.assign .local lNi (.const 1))
       (.while (.cmp .lower (vv lNi) (vv lNn))
         (.seq (.assign .local lNh (mixExp (vv lNh) (.load .one (.op .add [vv lNa, .shift .lsl (vv lNi) (.const 3)]))))
           (.assign .local lNi (.op .add [vv lNi, .const 1]))))))
    (.assign .local lNh (.const 0))

/-- The words' fold: `0` for none. -/
def foldW : List UInt64 → UInt64
  | [] => 0
  | w :: ws => ws.foldl leanMixHash w

theorem leanNatHash_foldW (n : Nat) : leanNatHash n = foldW (natWords n) := by
  unfold leanNatHash; cases natWords n <;> rfl

section
variable {σ : Type}

def NI (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (ws : List UInt64) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧ u.topAddr = t.topAddr ∧
  (∀ y, y ≠ lNh → y ≠ lNi → u.locals.lookup y = t.locals.lookup y) ∧
  ∃ i, 1 ≤ i ∧ i ≤ ws.length ∧ u.locals.lookup lNi = some (.val (.word (BitVec.ofNat 64 i))) ∧
    u.locals.lookup lNh = some (.val (.word (foldW (ws.take i)).toBitVec))

theorem foldW_take_succ (ws : List UInt64) (i : Nat) (hi : 1 ≤ i) (h : i < ws.length) :
    foldW (ws.take (i + 1)) = leanMixHash (foldW (ws.take i)) ws[i] := by
  match ws, i, hi, h with
  | w :: ws, i + 1, _, h =>
    simp only [List.take_succ_cons, foldW]
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp at h; omega), Option.toList_some, List.foldl_append]
    simp

theorem natHashP_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (ws : List UInt64) (hL : ws.length < 2 ^ 60)
    (hW : Words t A (ws.map UInt64.toBitVec))
    (la : t.locals.lookup lNa = some (.val (.word A)))
    (ln : t.locals.lookup lNn = some (.val (.word (BitVec.ofNat 64 ws.length))))
    (lh : ∃ w, t.locals.lookup lNh = some (.val (.word w))) (li : ∃ w, t.locals.lookup lNi = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState t natHashP).1 ∨ ((evaluateHOLFiniteState t natHashP).1 = none ∧
      (evaluateHOLFiniteState t natHashP).2.memory = t.memory ∧
      (evaluateHOLFiniteState t natHashP).2.memaddrs = t.memaddrs ∧
      (evaluateHOLFiniteState t natHashP).2.code = t.code ∧ (evaluateHOLFiniteState t natHashP).2.globals = t.globals ∧
      (evaluateHOLFiniteState t natHashP).2.topAddr = t.topAddr ∧
      (∀ y, y ≠ lNh → y ≠ lNi → (evaluateHOLFiniteState t natHashP).2.locals.lookup y = t.locals.lookup y) ∧
      (evaluateHOLFiniteState t natHashP).2.locals.lookup lNh = some (.val (.word (foldW ws).toBitVec))) := by
  obtain ⟨wh, hwh⟩ := lh; obtain ⟨wi, hwi⟩ := li
  unfold natHashP
  rw [ite_word t _ _ _ _ (eval_vv t lNn _ ln)]
  by_cases h0 : ws.length = 0
  · have : ws = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    simp only [show BitVec.ofNat 64 ([] : List UInt64).length = 0 from rfl, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [ConsLoop.assign_local t lNh (.const 0) 0 wh (eval_const t 0) hwh]
    exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y a1 _ => by lk, by lk; rfl⟩
  have hne : BitVec.ofNat 64 ws.length ≠ 0 := fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega)
  simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
  obtain ⟨w0, rest, hws⟩ : ∃ w0 rest, ws = w0 :: rest := by
    cases ws with | nil => simp at h0 | cons a b => exact ⟨a, b, rfl⟩
  have hw0 : t.memaddrs (A + BitVec.ofNat 64 (8 * 0)) ∧ t.memory (A + BitVec.ofNat 64 (8 * 0)) = .word w0.toBitVec := by
    have := hW 0 (by simp; omega); simp only [List.getElem_map] at this
    rw [show ws[0] = w0 by subst hws; rfl] at this; exact this
  rw [seq_normal _ (ConsLoop.assign_local t lNh _ w0.toBitVec wh
    (by rw [eval_load_word t _ _ (eval_vv t lNa _ la) (by simpa using hw0.1)]; simpa using hw0.2) hwh)]
  let t1 := setVarHOLFinite lNh (.val (.word w0.toBitVec)) t
  rw [seq_normal _ (ConsLoop.assign_local t1 lNi (.const 1) 1 wi (eval_const t1 1) (by lk [t1]; exact hwi))]
  let t2 := setVarHOLFinite lNi (.val (.word 1)) t1
  have hI : NI t A ws t2 := ⟨rfl, rfl, rfl, rfl, rfl, fun y a1 a2 => by lk [t2, t1], 1, Nat.le_refl _,
    by omega, lookup_setVar_same _ _ _, by lk [t2, t1]; rw [hws]; rfl⟩
  have := while_stop (.cmp .lower (vv lNi) (vv lNn))
    (.seq (.assign .local lNh (mixExp (vv lNh) (.load .one (.op .add [vv lNa, .shift .lsl (vv lNi) (.const 3)]))))
      (.assign .local lNi (.op .add [vv lNi, .const 1])))
    (NI t A ws) (fun u => NI t A ws u ∧ u.locals.lookup lNh = some (.val (.word (foldW ws).toBitVec)))
    (fun u hu => by
      obtain ⟨m0, d0, c0, g0, ta0, fr, i, hi1, hil, hni, hnh⟩ := id hu
      have hnn : u.locals.lookup lNn = some (.val (.word (BitVec.ofNat 64 ws.length))) := by
        rw [fr _ (by decide) (by decide)]; exact ln
      have hc : @evalHOLFinite 64 σ _ u (fun a => Classical.propDecidable (u.memaddrs a))
          (.cmp .lower (vv lNi) (vv lNn)) = some (.val (.word (bw (i < ws.length)))) := by
        simp only [evalHOLFinite]
        rw [ConsLoop.eval_cmp_of u .lower _ _ _ _ (eval_vv u lNi _ hni) (eval_vv u lNn _ hnn)]
        have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length) ↔ i < ws.length := by
          rw [BitVec.lt_def]; simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        by_cases h : i < ws.length
        · simp only [bw, h, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true (e.mpr h)]
        · simp only [bw, h, ↓reduceIte, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            decide_eq_false (fun x => h (e.mp x)), Bool.false_eq_true]
      by_cases h : i < ws.length
      · refine ⟨1, by rw [hc]; simp [bw, h], fun e => absurd e (by decide), fun _ _ => Or.inr ?_⟩
        let v := decClockHOLFinite u
        have hwi := hW i (by simp; exact h)
        have hld : @evalHOLExact 64 σ _ v.toExact (fun a => Classical.propDecidable (v.memaddrs a))
            (.load .one (.op .add [vv lNa, .shift .lsl (vv lNi) (.const 3)])) = some (.val (.word ws[i].toBitVec)) := by
          rw [eval_load_word v _ (A + BitVec.ofNat 64 (8 * i))
            (by rw [eval_add2 v _ _ _ _ (eval_vv v lNa _ (by show u.locals.lookup _ = _; rw [fr _ (by decide) (by decide)]; exact la))
                  (eval_shl v _ _ _ (eval_vv v lNi _ hni) (by decide)),
                show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)])
            (by show u.memaddrs _; rw [d0]; exact hwi.1)]
          show some (ValueHOL.val (u.memory _)) = _; rw [m0, hwi.2]; simp
        rw [seq_normal _ (ConsLoop.assign_local v lNh _ (leanMixHash (foldW (ws.take i)) ws[i]).toBitVec _
          (eval_mixExp v _ _ _ _ (eval_vv v lNh _ hnh) hld) hnh)]
        let v1 := setVarHOLFinite lNh (.val (.word (leanMixHash (foldW (ws.take i)) ws[i]).toBitVec)) v
        have hni1 : v1.locals.lookup lNi = some (.val (.word (BitVec.ofNat 64 i))) := by lk [v1]; exact hni
        rw [ConsLoop.assign_local v1 lNi _ (BitVec.ofNat 64 (i + 1)) _
          (by rw [eval_add2 v1 _ _ _ _ (eval_vv v1 lNi _ hni1) (eval_const v1 1)]
              congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) hni1]
        exact ⟨rfl, m0, d0, c0, g0, ta0, fun y a1 a2 => by lk [v1, v]; exact fr y a1 a2, i + 1, by omega, by omega,
          by lk, by lk [v1]; rw [foldW_take_succ ws i hi1 h]⟩
      · refine ⟨0, by rw [hc]; simp only [bw, h, ↓reduceIte], fun _ => ⟨hu, ?_⟩, fun e => absurd rfl e⟩
        rw [hnh, show i = ws.length by omega, List.take_length])
    t2 hI
  rcases this with hs | ⟨h1, ⟨m, d, c, g, ta, fr, _⟩, hh⟩
  · exact Or.inl hs
  · exact Or.inr ⟨h1, m, d, c, g, ta, fr, hh⟩

end

end ConPanqueque.V
