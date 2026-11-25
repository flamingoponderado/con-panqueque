import ConPanqueque.Front.Top

/-! # The program after its read

`rest_verdict`: `top_verdict` from the state after the read, for a context whose value heap is the
read's image `writeH Hb … nb` of some heap `Hb` (the pin phase runs between the read and the rest,
and leaves the value heap as the read left it). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan ConPanqueque.T.Decl ConRon.Bridge

variable {σ : Type}

theorem rest_verdict (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : ConRon.Bridge.PersPins s) (hpins : ConRon.Bridge.PinsDenote s.store pins pinsP)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1, kBN, kBA], x ∈ D)
    (rb capD jN cap j0 Lw : Nat)
    (hlay : jN + 3 * cap ≤ rb) (hbuf0 : rb + 1 + capD ≤ j0 + 1) (Hb : List (BitVec 64)) (hcells : j0 + Lw ≤ Hb.length)
    (hL16 : 16 ≤ 8 * Lw) (h59 : 8 * Lw < 2 ^ 59)
    (hal : (cellA C j0).toNat % 8 = 0) (hov : (cellA C j0).toNat + 8 * Lw + 8 < 2 ^ 64)
    (hbits : System.Platform.numBits = 64)
    (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hRA : Γ.get kRA = some (cellA C j0)) (hRL : Γ.get kRL = some (BitVec.ofNat 64 (8 * Lw)))
    (hRM : Γ.get kRM = some (BitVec.ofNat 64 (8 * Lw - 16)))
    (nb : List (BitVec 8)) (hl : nb.length = 8 * Lw) (hH : C.H = writeH Hb (cellA C j0) j0 0 nb)
    (t : PState σ) (ht : Inv C s Γ M D t) :
    Stop (evaluateHOLFiniteState t restP).1 ∨
      ((∃ w, (evaluateHOLFiniteState t restP).1 = some (.returned (.val (.word w)))) ∧
        ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
          ∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP rc.decls.toList
            = .ok (ConLeche.streamEnv rc.decls.toList)) := by
  let Cp := ctxH C Hb
  have eC : C = ctxH Cp (writeH Hb (cellA C j0) j0 0 nb) := by
    simp only [Cp]; rw [ctxH_ctxH, ← hH, ctxH_self]
  have hokp : CtxOK Cp := ctxOK_H hok Hb
  let H' := writeH Hb (cellA C j0) j0 0 nb
  let C1 := ctxH Cp H'
  have hH'l : H'.length = Hb.length := writeH_length _ _ _ _ _
  have hj0 : j0 < C1.H.length := by show j0 < H'.length; omega
  have hinv : Inv C1 s Γ [] D t := by
    have e : C1 = C := eC.symm
    rw [e]; exact ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  -- the length load
  unfold restP
  rcases step_heapLoadI (C := C1) kBN (vv kRA) j0 hj0 (hD _ (by simp)) (by show Γ.get kRA = some (cellA C j0); exact hRA)
      t hinv with
    hs1 | ⟨hn1, hinv1⟩
  · exact Or.inl (seq_stop _ _ _ hs1)
  generalize ht2 : (evaluateHOLFiniteState t (.assign .local kBN (.load .one (vv kRA)))).2 = t2 at hinv1
  have e2 := seq_normal (s := t) (s₁ := t2)
    (.ite (.cmp .lower (vv kBN) (vv kRM)) (.seq (.assign .local kBA (.op .add [vv kRA, .const 8])) mainP) hang)
    (by rw [← hn1, ← ht2])
  rw [e2]
  let w := C1.H[j0]
  have hw : w = BitVec.ofNat 64 w.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hwv : w.toNat = leNat (nb.take 8) := by
    have := header_value Hb (cellA C j0) j0 hal nb (by omega) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (show j0 < H'.length by omega), Option.getD_some] at this; exact this
  let Γ2 : Env := (kBN, w) :: Γ
  have hg : sev Γ2 (.cmp .lower (vv kBN) (vv kRM)) = some (bw (w.toNat < 8 * Lw - 16)) :=
    sev_lower Γ2 (vv kBN) (vv kRM) w.toNat (8 * Lw - 16) (by simp [Γ2, sev, vv, Env.get_cons]) (by
      simp only [sev, vv, Γ2, Env.get_cons, ite_eq_right (show kRM ≠ kBN by decide)]; exact hRM) w.isLt (by omega)
  rw [ite_word t2 _ _ _ _ (inv_ev hinv1 hg)]
  by_cases hgd : w.toNat < 8 * Lw - 16
  swap
  · rw [ite_eq_right (by simp [bw, hgd])]; exact Or.inl (stop_hang _)
  rw [ite_eq_left (by simp [bw, hgd])]
  rcases step_assignI (C := C1) kBA (.op .add [vv kRA, .const 8]) (cellA C1 (j0 + 1)) (hD _ (by simp)) (by
      simp only [sev, vv, Γ2, Env.get_cons, ite_eq_right (show kRA ≠ kBN by decide), hRA, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
      rw [show cellA C1 (j0 + 1) = cellA C j0 + BitVec.ofNat 64 (8 * 1) from cellA_add C j0 1]; rfl) t2 hinv1 with
    hs3 | ⟨hn3, hinv3⟩
  · exact Or.inl (seq_stop _ _ _ hs3)
  generalize ht3 : (evaluateHOLFiniteState t2 (.assign .local kBA (.op .add [vv kRA, .const 8]))).2 = t3 at hinv3
  have e3 := seq_normal (s := t2) (s₁ := t3) mainP (by rw [← hn3, ← ht3])
  rw [e3]
  -- the parse and the fold
  let b := inputOf nb w.toNat
  have hbsz : b.size = w.toNat := inputOf_size nb _ (by omega)
  have hbuf : BufOK C1 (j0 + 1) b := bufOK_of_read Cp j0 Lw hal hcells (by show (cellA C j0).toNat + 8 * Lw < 2 ^ 64; omega) h59 hbits nb hl _ (by omega)
  let Γ3 : Env := (kBA, cellA C1 (j0 + 1)) :: Γ2
  have g3 : ∀ y, y ≠ kBA → y ≠ kBN → Γ3.get y = Γ.get y := fun y h1 h2 => by
    simp only [Γ3, Γ2, Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  rcases front_verdict (F := j0 + Lw) (rb := rb) (capD := capD) (jN := jN) (cap := cap) (bufJ := j0 + 1) (b := b)
      pins pinsP ra C1 (ctxOK_ctxH hokp) (frontOK_ctxH (frontOK_H hf Hb)) (frontCodes_ctxH (frontCodes_ctxH fc)) (foldCodes_ctxH (foldCodes_ctxH hc Hb) H') hs hpl hfe hcF
      s hst hoff hpo hpp hpins Γ3 [] D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp))
      ⟨by omega, by omega, by omega, hbuf0, by rw [hbsz]; omega⟩ hcap1 hcapN hcap8 hcapD8
      (by show j0 + Lw ≤ H'.length; omega) hbuf
      (by rw [g3 _ (by decide) (by decide)]; exact hZb) (by rw [g3 _ (by decide) (by decide)]; exact hZn)
      (by rw [g3 _ (by decide) (by decide)]; exact hTN) (by rw [g3 _ (by decide) (by decide)]; exact hTL)
      (by rw [g3 _ (by decide) (by decide)]; exact hTE) (by rw [g3 _ (by decide) (by decide)]; exact hC)
      (by simp [Γ3, Env.get_cons])
      (by simp only [Γ3, Γ2, Env.get_cons, ite_eq_right (show kBN ≠ kBA by decide), ite_eq_left]; rw [hbsz, ← hw])
      (by rw [g3 _ (by decide) (by decide)]; exact hRB) (by rw [g3 _ (by decide) (by decide)]; exact hCD)
      (by rw [g3 _ (by decide) (by decide)]; exact hZL) t3 hinv3 with hs4 | ⟨hret, rc, hrc, hacc⟩
  · exact Or.inl hs4
  · refine Or.inr ⟨hret, rc, ?_, hacc⟩
    rw [← hwv]; exact hrc

end ConPanqueque.Front
