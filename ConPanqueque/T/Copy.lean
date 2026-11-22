import ConPanqueque.T.Blk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Copying words between heap cells

`copyLoop`: `while (i < n) { z := *src; *dst := z; src += 8; dst += 8; i += 1 }`, copying `n` words of
an existing block into cells the caller owns; the image after `i` iterations is `fillI B ws o i`.
-/

namespace ConPanqueque.T

variable {σ : Type}

/-- The image `B` with its cells `o … o + i - 1` replaced by the first `i` words of `ws`. -/
def fillI (B ws : List (BitVec 64)) (o : Nat) : Nat → List (BitVec 64)
  | 0 => B
  | i + 1 => (fillI B ws o i).set (o + i) (ws.getD i 0)

theorem fillI_length (B ws : List (BitVec 64)) (o : Nat) : ∀ i, (fillI B ws o i).length = B.length
  | 0 => rfl
  | i + 1 => by simp [fillI, fillI_length B ws o i]

theorem fillI_get? (B ws : List (BitVec 64)) (o : Nat) : ∀ i k, (fillI B ws o i)[k]? =
    if o ≤ k ∧ k < o + i ∧ k < B.length then some (ws.getD (k - o) 0) else B[k]?
  | 0, k => by simp [fillI]; intro _ h; omega
  | i + 1, k => by
    simp only [fillI, List.getElem?_set, fillI_length, fillI_get? B ws o i k]
    by_cases e : o + i = k
    · subst e; by_cases h : o + i < B.length <;> simp [h]
    · simp only [e, ite_false]
      by_cases h1 : o ≤ k ∧ k < o + i ∧ k < B.length
      · rw [if_pos h1, if_pos ⟨h1.1, by omega, h1.2.2⟩]
      · rw [if_neg h1, if_neg (by omega)]

theorem inv_envMono {C : Ctx} {s : AState} {Γ Γ' : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ' M D t) (hg : ∀ x v, Γ.get x = some v → Γ'.get x = some v) : Inv C s Γ M D t :=
  ⟨h.sr, fun x v hx => h.env x v (hg x v hx), h.mem, h.decl⟩

def lSrc := ofString "csrc"
def lDst := ofString "cdst"
def lCi := ofString "ci"
def lCz := ofString "cz"
def lCn := ofString "cn"

def copyLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv lCi) (vv lCn))
    (.seq (.assign .local lCz (.load .one (vv lSrc)))
      (.seq (.store (vv lDst) (vv lCz))
        (.seq (.assign .local lSrc (.op .add [vv lSrc, .const 8]))
          (.seq (.assign .local lDst (.op .add [vv lDst, .const 8]))
            (.assign .local lCi (.op .add [vv lCi, .const 1]))))))

theorem cellA_add8 (C : Ctx) (k : Nat) : cellA C k + 8 = cellA C (k + 1) := by
  simp only [cellA, BitVec.add_assoc]
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1

/-- The copy: source block words `ws` at `os …`, destination cells `od …` (owned, above the source). -/
theorem specR_copyI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (B ws : List (BitVec 64)) (os od : Nat) (hD : lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : ∀ j (hj : j < ws.length), B[os + j]? = some ws[j]) (hdis : os + ws.length ≤ od)
    (hdst : od + ws.length ≤ B.length) (hn : ws.length < 2 ^ 63)
    (hCn : Γ.get lCn = some (BitVec.ofNat 64 ws.length))
    (hne : lCn ≠ lSrc ∧ lCn ≠ lDst ∧ lCn ≠ lCi ∧ lCn ≠ lCz) (hz : Γ.get lCz = none)
    (hr : SpecR (Inv (ctxH C (fillI B ws od ws.length)) s ((lCi, BitVec.ofNat 64 ws.length) ::
      (lDst, cellA C (od + ws.length)) :: (lSrc, cellA C (os + ws.length)) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C B) s ((lCi, BitVec.ofNat 64 0) :: (lDst, cellA C (od + 0)) :: (lSrc, cellA C (os + 0)) :: Γ)
      [] D) (.seq copyLoop rest) s m R := by
  have hl := fillI_length B ws od
  refine specR_forI (σ := σ) (D := D) _ _ rest ws.length (fun i => ctxH C (fillI B ws od i))
    (fun i => (lCi, BitVec.ofNat 64 i) :: (lDst, cellA C (od + i)) :: (lSrc, cellA C (os + i)) :: Γ)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 ws.length)
      then 1 else 0, by simp [sev, hCn, hne.2.2.1, hne.2.1, hne.1], ?_⟩) (fun i hi => ?_) hr
  · have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length) ↔ i < ws.length := by
      rw [BitVec.lt_def]; simp; omega
    by_cases h : i < ws.length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h, h]
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length := fun x => h (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h]
  -- one iteration
  have hsi : os + i < (ctxH C (fillI B ws od i)).H.length := by
    show os + i < (fillI B ws od i).length; rw [hl]; omega
  have hvi : (ctxH C (fillI B ws od i)).H[os + i]'hsi = ws[i] := by
    have := fillI_get? B ws od i (os + i)
    rw [if_neg (by omega), hsrc i hi] at this
    show (fillI B ws od i)[os + i] = ws[i]
    rw [List.getElem?_eq_getElem (by rw [hl]; omega)] at this; exact Option.some.inj this
  have hdi : od + i < (ctxH C (fillI B ws od i)).H.length := by
    show od + i < (fillI B ws od i).length; rw [hl]; omega
  refine step_seq (step_heapLoadI (C := ctxH C (fillI B ws od i)) lCz (vv lSrc) (os + i) hsi hD.2.2.2
    (by simp +decide [cellA, ctxH])) ?_
  rw [hvi]
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv lDst) (vv lCz) (od + i) hdi ws[i]
    (by simp +decide [cellA, ctxH]) (by simp)) ?_
  refine step_seq (step_assignI lSrc _ (cellA C (os + i + 1)) hD.1 (by simp +decide [sev]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI lDst _ (cellA C (od + i + 1)) hD.2.1 (by simp +decide [sev]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI lCi _ (BitVec.ofNat 64 (i + 1)) hD.2.2.1 (by simp +decide [sev]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => ?_)
  have e : (fillI B ws od i).set (od + i) ws[i] = fillI B ws od (i + 1) := by
    simp [fillI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  refine inv_envMono (by rw [← e]; exact ht) (fun x v hx => ?_)
  simp only [Env.get_cons] at hx ⊢
  by_cases h1 : x = lCi
  · simp_all
  by_cases h2 : x = lDst
  · subst h2; simp_all [show lDst ≠ lCi by decide, show lDst ≠ lSrc by decide, Nat.add_assoc]
  by_cases h3 : x = lSrc
  · subst h3; simp_all [show lSrc ≠ lCi by decide, show lSrc ≠ lDst by decide, Nat.add_assoc]
  by_cases h4 : x = lCz
  · subst h4; simp_all
  simp_all

end ConPanqueque.T
