import ConPanqueque.T.NView
import ConPanqueque.T.Copy
import ConPanqueque.T.Ex.Small
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Name equality by structure

`neq(a, b)`: equal handles answer `1`; otherwise both rows are read, compared from their second word
on (the string bytes or the number's limbs), and the prefixes compared recursively. It decides the
equality of the names the handles read back to, with no well-formedness assumption on the store.
-/

namespace ConPanqueque.T.NEq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM

def fNeq := ofString "nameEq"
def pNa := ofString "na"
def pNb := ofString "nb"

/-- `w := w ∧ row₁[i] = row₂[i]` for `i` from `bb` up to the row length. -/
def cmpLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv lB) (vv lRn))
    (.seq (.assign .local lX (.load .one (.op .add [vv lA1, .shift .lsl (vv lB) (.const 3)])))
      (.seq (.assign .local lY (.load .one (.op .add [vv lRp, .shift .lsl (vv lB) (.const 3)])))
        (.seq (.assign .local lW (.op .and [vv lW, .cmp .equal (vv lX) (vv lY)]))
          (.assign .local lB (.op .add [vv lB, .const 1])))))

/-- The flag after comparing words `1 … i` (`i` words). -/
def flagW (ws1 ws2 : List (BitVec 64)) (i : Nat) : BitVec 64 :=
  if ∀ j, j < i → ws1[j + 1]? = ws2[j + 1]? then 1 else 0

section
variable {σ : Type}

theorem flagW_succ (ws1 ws2 : List (BitVec 64)) (i : Nat) (h1 : i + 1 < ws1.length) (h2 : i + 1 < ws2.length) :
    flagW ws1 ws2 (i + 1) = flagW ws1 ws2 i &&&
      (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal ws1[i + 1] ws2[i + 1] then 1 else 0) := by
  unfold flagW
  by_cases hA : ∀ j, j < i → ws1[j + 1]? = ws2[j + 1]?
  · by_cases e : ws1[i + 1] = ws2[i + 1]
    · have : ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := by
        intro j hj
        rcases Nat.lt_or_ge j i with hl | hg
        · exact hA j hl
        · have : j = i := by omega
          subst this; rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, e]
      rw [if_pos this, if_pos hA]; simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : ¬ ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := by
        intro h; have := h i (by omega)
        rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this; exact e (Option.some.inj this)
      rw [if_neg this, if_pos hA]; simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : ¬ ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := fun h => hA (fun j hj => h j (by omega))
    rw [if_neg this, if_neg hA]; simp

theorem cmpLoop_spec {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (ws1 ws2 : List (BitVec 64)) (P1 P2 : BitVec 64)
    (hlen : ws1.length = ws2.length) (hpos : 1 ≤ ws1.length) (hn : ws1.length < 2 ^ 60)
    (hm1 : ∀ i (hi : i < ws1.length), (P1 + BitVec.ofNat 64 (8 * i), ws1[i]) ∈ M)
    (hm2 : ∀ i (hi : i < ws2.length), (P2 + BitVec.ofNat 64 (8 * i), ws2[i]) ∈ M)
    (ha1 : Γ.get lA1 = some P1) (hrp : Γ.get lRp = some P2) (hrn : Γ.get lRn = some (BitVec.ofNat 64 ws1.length))
    (hx : Γ.get lX = none) (hy : Γ.get lY = none)
    (hr : SpecR (Inv C s ((lB, BitVec.ofNat 64 ws1.length) :: (lW, flagW ws1 ws2 (ws1.length - 1)) :: Γ) M DI)
      rest s m R) :
    SpecR (Inv C s ((lB, BitVec.ofNat 64 (0 + 1)) :: (lW, flagW ws1 ws2 0) :: Γ) M DI) (.seq cmpLoop rest) s m R := by
  have hr' : SpecR (Inv C s ((lB, BitVec.ofNat 64 ((ws1.length - 1) + 1)) ::
      (lW, flagW ws1 ws2 (ws1.length - 1)) :: Γ) M DI) rest s m R := by
    rw [show ws1.length - 1 + 1 = ws1.length by omega]; exact hr
  refine specR_forI (σ := σ) (D := DI) (M := M) _ _ rest (ws1.length - 1) (fun _ => C)
    (fun i => (lB, BitVec.ofNat 64 (i + 1)) :: (lW, flagW ws1 ws2 i) :: Γ)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (i + 1))
      (BitVec.ofNat 64 ws1.length) then 1 else 0, by simp +decide [sev, hrn], ?_⟩) (fun i hi => ?_) hr'
  · have e : (BitVec.ofNat 64 (i + 1) < BitVec.ofNat 64 ws1.length) ↔ i + 1 < ws1.length := by
      rw [BitVec.lt_def]; simp; omega
    by_cases h : i + 1 < ws1.length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]; omega
    · have : ¬ BitVec.ofNat 64 (i + 1) < BitVec.ofNat 64 ws1.length := fun x => h (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]; omega
  have hi1 : i + 1 < ws1.length := by omega
  have hi2 : i + 1 < ws2.length := by omega
  have addr : ∀ P : BitVec 64, P + BitVec.ofNat 64 (i + 1) <<< (3 : BitVec 64).toNat = P + BitVec.ofNat 64 (8 * (i + 1)) := by
    intro P; rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  refine step_seq (step_loadI lX _ (P1 + BitVec.ofNat 64 (8 * (i + 1))) ws1[i + 1] (by decide)
    (by simp +decide [sev, ha1]; rw [shl_ofNat _ _ (by omega)]) (hm1 _ hi1)) ?_
  refine step_seq (step_loadI lY _ (P2 + BitVec.ofNat 64 (8 * (i + 1))) ws2[i + 1] (by decide)
    (by simp +decide [sev, hrp]; rw [shl_ofNat _ _ (by omega)]) (hm2 _ hi2)) ?_
  refine step_seq (step_assignI lW _ (flagW ws1 ws2 (i + 1)) (by decide)
    (by simp +decide [sev]; rw [flagW_succ ws1 ws2 i hi1 hi2]; rfl)) ?_
  refine step_mono (step_assignI lB _ (BitVec.ofNat 64 (i + 1 + 1)) (by decide)
    (by simp +decide [sev]; exact word_add1_eq (i + 1))) (fun _ h => h) (fun t ht => ?_)
  refine inv_envMono ht (fun z v hz => ?_)
  simp only [Env.get_cons] at hz ⊢
  by_cases h1 : z = lB
  · simp_all
  by_cases h2 : z = lW
  · subst h2; simp_all [show lW ≠ lB by decide]
  by_cases h3 : z = lY
  · subst h3; simp_all
  by_cases h4 : z = lX
  · subst h4; simp_all
  simp_all

end

end ConPanqueque.T.NEq
