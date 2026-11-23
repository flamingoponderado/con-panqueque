import ConPanqueque.T.Copy
import ConPanqueque.T.Env
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Copying from the environment heap into the value heap

Functions specified over value-heap blocks (e.g. `instLPFast`'s level-parameter names) take an
environment block by copy: the same loop as `T/Copy.lean`, its source in the environment heap.
-/

namespace ConPanqueque.T

section
variable {σ : Type}

theorem step_envLoadI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64) (j : Nat)
    (w : BitVec 64) (hx : x ∈ D) (he : sev Γ e = some (ecell C j)) (hw : C.EH[j]? = some w) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, w) :: Γ) M D) := by
  intro t ht
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  obtain ⟨w0, h0⟩ := ht.decl x hx
  have hE := ht.sr.env.1
  have hev : EV t (.load .one e) = some (.val (.word w)) := by
    rw [EV, eval_load_word t _ _ (inv_ev ht he) (hE.dom j (Nat.lt_of_lt_of_le hj hE.len))]
    have := hE.val j hj
    unfold ecell
    rw [this, hjw]
  rw [ConsLoop.assign_local t x _ w w0 hev h0]
  exact Or.inr ⟨rfl, inv_set ht x w⟩

theorem ecell_add8 (C : Ctx) (k : Nat) : ecell C k + 8 = ecell C (k + 1) := by
  simp only [ecell, BitVec.add_assoc]
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]; congr 1

/-- The copy: source words `ws` at environment cells `os …`, destination value-heap cells `od …` (owned). -/
theorem specR_copyEI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (B ws : List (BitVec 64)) (os od : Nat) (hD : lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : ∀ j (hj : j < ws.length), C.EH[os + j]? = some ws[j])
    (hdst : od + ws.length ≤ B.length) (hn : ws.length < 2 ^ 63)
    (hCn : Γ.get lCn = some (BitVec.ofNat 64 ws.length))
    (hne : lCn ≠ lSrc ∧ lCn ≠ lDst ∧ lCn ≠ lCi ∧ lCn ≠ lCz) (hz : Γ.get lCz = none)
    (hr : SpecR (Inv (ctxH C (fillI B ws od ws.length)) s ((lCi, BitVec.ofNat 64 ws.length) ::
      (lDst, cellA C (od + ws.length)) :: (lSrc, ecell C (os + ws.length)) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C B) s ((lCi, BitVec.ofNat 64 0) :: (lDst, cellA C (od + 0)) :: (lSrc, ecell C (os + 0)) :: Γ)
      [] D) (.seq copyLoop rest) s m R := by
  have hl := fillI_length B ws od
  refine specR_forI (σ := σ) (D := D) _ _ rest ws.length (fun i => ctxH C (fillI B ws od i))
    (fun i => (lCi, BitVec.ofNat 64 i) :: (lDst, cellA C (od + i)) :: (lSrc, ecell C (os + i)) :: Γ)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 ws.length)
      then 1 else 0, by simp [sev, hCn, hne.2.2.1, hne.2.1, hne.1], ?_⟩) (fun i hi => ?_) hr
  · have e : (BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length) ↔ i < ws.length := by
      rw [BitVec.lt_def]; simp; omega
    by_cases h : i < ws.length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h, h]
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length := fun x => h (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h]
  have hdi : od + i < (ctxH C (fillI B ws od i)).H.length := by
    show od + i < (fillI B ws od i).length; rw [hl]; omega
  refine step_seq (step_envLoadI (C := ctxH C (fillI B ws od i)) lCz (vv lSrc) (os + i) ws[i] hD.2.2.2
    (by simp +decide [ecell, ctxH]) (hsrc i hi)) ?_
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv lDst) (vv lCz) (od + i) hdi ws[i]
    (by simp +decide [cellA, ctxH]) (by simp)) ?_
  refine step_seq (step_assignI lSrc _ (ecell C (os + i + 1)) hD.1 (by simp +decide [sev]; exact ecell_add8 C _)) ?_
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

end

end ConPanqueque.T
