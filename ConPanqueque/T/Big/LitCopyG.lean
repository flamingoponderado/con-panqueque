import ConPanqueque.T.Big.LitCopy
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Copying any view row's payload

`litBody` copies the words after a view row's first word into a fresh block. `litg_spec`: for any handle whose
row is `w0 :: ws`, the block holds `ws` (state unchanged). Used for a string literal's bytes.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot

section
variable {σ : Type}

/-- The post of a helper returning a fresh block holding `ws` (state unchanged). -/
def PostG (C : Ctx) (s : AState) (ws : List (BitVec 64)) (_ : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o ws ∧ s' = s ∧ SR (ctxH C H') s st

theorem postG_locals (C : Ctx) (s : AState) (ws : List (BitVec 64)) : ∀ (a : Unit) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostG C s ws a w s' st → PostG C s ws a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, hb, hs, hsr⟩ => ⟨H', o, hp, hw, hb, hs, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem litg_loop {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (h : EIdx) (v : ENodeView) (w0 : BitVec 64) (ws : List (BitVec 64))
    (hv : s.store.view h = some v) (hev : encEView v = w0 :: ws) (B0 : List (BitVec 64)) (od : Nat)
    (hdst : od + 1 + ws.length ≤ B0.length) (h61 : ws.length < 2 ^ 61)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D ∧ cX ∈ D ∧ cQ ∈ D ∧ cK ∈ D ∧ cI ∈ D)
    (hln : Γ0.get cLn = some (BitVec.ofNat 64 ws.length)) (hdh : Γ0.get lDh = some (Enc.idxW h))
    (hfl : Γ0.get lFl = some C.FLe) (hdir : Γ0.get lDir = some C.L.DIR)
    (hn : Γ0.get lRp = none ∧ Γ0.get lRn = none ∧ Γ0.get lDt = none ∧ Γ0.get lDg = none ∧ Γ0.get lDi = none ∧
      Γ0.get cX = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 ws (od + 1) ws.length)) s
      (litG Γ0 C od ws.length) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 ws (od + 1) 0)) s (litG Γ0 C od 0) [] D) (.seq litLoop rest) s m R := by
  obtain ⟨d1, d2, d3, d4, d5, dx, dq, dk, di⟩ := hD
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn
  have hl := fillI_length B0 ws (od + 1)
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest ws.length
    (fun i => ctxH C (fillI B0 ws (od + 1) i)) (litG Γ0 C od)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 ws.length) then 1 else 0, by simp [sev, litG, Env.get, hln], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i ws.length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < ws.length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 ws.length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_eViewI (C := ctxH C (fillI B0 ws (od + 1) i)) h _ hv
    (by simp [litG, hdh]) (by simp [litG, hfl]; rfl) (by simp [litG, hdir]; rfl) ⟨d1, d2, d3, d4, d5⟩) ?_
  refine step_ex fun P => ?_
  simp only [hev]
  refine step_seq (step_loadI cX _ (P + BitVec.ofNat 64 (8 * (i + 1))) ws[i] dx
    (by simp [sev, litG]) (wordsAt_get P (w0 :: ws) (i + 1) (by simp; omega) [])) ?_
  have hdi : od + 1 + i < (ctxH C (fillI B0 ws (od + 1) i)).H.length := by
    show od + 1 + i < (fillI B0 ws (od + 1) i).length; rw [hl]; omega
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv cQ) (vv cX) (od + 1 + i) hdi ws[i]
    (by simp [litG]; rfl) (by simp)) ?_
  refine step_seq (step_assignI cQ _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, litG]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI cK _ (BitVec.ofNat 64 (8 * (i + 1 + 1))) dk
    (by simp [sev, litG]; exact ofNat8_succ i)) ?_
  refine step_mono (step_assignI cI _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, litG]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => ?_)
  have e : (fillI B0 ws (od + 1) i).set (od + 1 + i) ws[i] = fillI B0 ws (od + 1) (i + 1) := by
    simp [fillI, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  refine inv_envMono (by rw [← e]; exact ht) (fun x v hx => ?_)
  simp only [litG, Env.get_cons] at hx ⊢
  by_cases e1 : x = cI
  · subst e1; simp_all
  by_cases e2 : x = cK
  · subst e2; simp_all
  by_cases e3 : x = cQ
  · subst e3; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, ite_false] at hx
  have f1 : x ≠ cX := by intro e; subst e; rw [n6] at hx; simp at hx
  have f2 : x ≠ lRp := by intro e; subst e; rw [n1] at hx; simp at hx
  have f3 : x ≠ lRn := by intro e; subst e; rw [n2] at hx; simp at hx
  have f4 : x ≠ lDt := by intro e; subst e; rw [n3] at hx; simp at hx
  have f5 : x ≠ lDg := by intro e; subst e; rw [n4] at hx; simp at hx
  have f6 : x ≠ lDi := by intro e; subst e; rw [n5] at hx; simp at hx
  simp [e1, e2, e3, f1, f2, f3, f4, f5, f6, hx]

theorem litg_spec (C : Ctx) (hok : CtxOK C) (s : AState) (h : EIdx) (v : ENodeView) (w0 : BitVec 64) (ws : List (BitVec 64))
    (hv : s.store.view h = some v) (hev : encEView v = w0 :: ws) :
    SpecR (σ := σ) (Pre C s ([cH].zip [Enc.idxW h])) (litBody C) s (pure () : AM Unit) (PostG C s ws) := by
  refine specR_prologue (postG_locals C s ws) (lit_none C _) ?_
  unfold litCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv cH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun _ => (pure () : AM Unit))
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine ILP.specR_viewIv h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v' P hv' _ hl => ?_)
  rw [hv] at hv'; cases hv'
  rw [hev] at hl ⊢
  simp only [List.length_cons] at hl
  refine specR_assignI cLn _ (BitVec.ofNat 64 ws.length) (by decide)
    (by simp +decide [sev, Env.get]; exact Ex.ofNat_succ_sub_one _) ?_
  refine specR_allocI cO (.panop .mul [.op .add [vv cLn, .const 1], .const 8]) (ws.length + 1) (by omega)
    (by decide) (fun v => by simp [sev, Env.get]; rw [word_add1_eq]; exact CV.mul8_eq _) (fun H' wsN hpre hwl hcap => ?_)
  have hj : H'.length < (ctxH C (H' ++ wsN)).H.length := by show H'.length < (H' ++ wsN).length; simp; omega
  refine specR_heapStoreI (C := ctxH C (H' ++ wsN)) (ctxOK_H hok _) (vv cO) (vv cLn) H'.length hj
    (BitVec.ofNat 64 ws.length) (by simp; rfl) (by simp) ?_
  refine specR_assignI cQ _ (cellA C (H'.length + 1)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
  refine specR_assignI cK (.const 8) (BitVec.ofNat 64 (8 * (0 + 1))) (by decide) rfl ?_
  refine specR_assignI cI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  let B0 := (H' ++ wsN).set H'.length (BitVec.ofNat 64 ws.length)
  have hB0 : B0.length = H'.length + (ws.length + 1) := by simp [B0, hwl]
  refine specR_envWeak (Γb := litG ([(cLn, BitVec.ofNat 64 ws.length), (cO, cellA C H'.length),
    (lFl, C.FLe), (lDh, Enc.idxW h), (lDir, C.L.DIR)]) C H'.length 0) (fun x v hx => ?_) ?_
  · simp only [litG, Env.get_cons] at hx ⊢
    by_cases e1 : x = cI
    · subst e1; simpa using hx
    by_cases e2 : x = cK
    · subst e2; simpa using hx
    by_cases e3 : x = cQ
    · subst e3; simpa using hx
    by_cases e4 : x = cLn
    · subst e4; simpa using hx
    by_cases e5 : x = cO
    · subst e5; simpa using hx
    by_cases e6 : x = lFl
    · subst e6; simpa using hx
    by_cases e7 : x = lDh
    · subst e7; simp at hx; subst hx; simp
    by_cases e8 : x = lDir
    · subst e8; simp at hx; subst hx; simp [Env.get, ctxEnv]
    simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hx
  refine litg_loop (C := C) hok h v w0 ws hv hev B0 H'.length (by rw [hB0]; omega) (by omega)
    (by decide) (by simp) (by simp) (by simp) (by simp) (by simp +decide [Env.get]) ?_
  refine specR_returnI _ (cellA C H'.length) (by simp [litG]) (fun t ht => ?_)
  refine ⟨fillI B0 ws (H'.length + 1) ws.length, H'.length, ?_, rfl, ?_, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · exact CV.prefix_fillI _ _ _ C.H (by have := hpre.length_le; omega)
      (prefix_set_ge (hpre.trans (List.prefix_append _ _)) _ (hpre.length_le) _) _
  · have hl0 := fillI_length B0 ws (H'.length + 1)
    constructor
    · rw [fillI_get?, ite_eq_right (by omega)]
      show ((H' ++ wsN).set H'.length _)[H'.length]? = _
      rw [List.getElem?_set_self (show H'.length < (H' ++ wsN).length by simp; omega)]
    · intro i hi
      rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB0]; omega⟩]
      simp [show H'.length + 1 + i - (H'.length + 1) = i by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]

end

end ConPanqueque.T.Big
