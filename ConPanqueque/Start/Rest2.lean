import ConPanqueque.Start.Names
import ConPanqueque.Start.Rest

/-! # The program after its read, with the forbidden-name pass

`rest_verdict`: `top_verdict` from the state after the read, for a context whose value heap is the
read's image `writeH Hb … nb` of some heap `Hb` (the pin phase runs between the read and the rest,
and leaves the value heap as the read left it). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Start

open ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan ConPanqueque.T.Decl ConRon.Bridge

variable {σ : Type}

/-- `len / 16 + 2`: every id in an input of `len` bytes is below it (a record line has at least 17 bytes). -/
def capE : ExpHOL 64 := .op .add [.shift .lsr (vv kBN) (.const 4), .const 2]

/-- The id tables' capacity `min capM (len / 16 + 2)` (as `c0 + (capM - c0) · [capM < c0]`), and the tables'
places and zeroed span from it.  A smaller capacity only rejects more (the theorem is soundness only); sizing it
from the input keeps the start-up zeroing proportional to the input instead of `3 · capM` cells. -/
def capP (capM : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local fCap (.op .add [capE, .panop .mul [.op .sub [.const (BitVec.ofNat 64 capM), capE],
      .cmp .lower (.const (BitVec.ofNat 64 capM)) capE]]))
    (.seq (.assign .local kZn (.op .add [vv fCap, .op .add [vv fCap, vv fCap]]))
      (.seq (.assign .local fTL (.op .add [vv fTN, .shift .lsl (vv fCap) (.const 3)]))
        (.seq (.assign .local fTE (.op .add [vv fTL, .shift .lsl (vv fCap) (.const 3)])) rest)))

def restP2 (capM : Nat) : ProgHOL 64 :=
  .seq (.assign .local kBN (.load .one (vv kRA)))
    (.ite (.cmp .lower (vv kBN) (vv kRM))
      (.seq (.assign .local kBA (.op .add [vv kRA, .const 8])) (capP capM mainP2)) hang)

theorem rest_verdict2 (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hEB : ∀ j, ecell C j = ecb j)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s)
    (hpp : ConRon.Bridge.PersPins s) (hpins : ConRon.Bridge.PinsDenote s.store pins pinsP)
    (hA : denoteN s.store.ns default = some .anonymous)
    (hb : PinBlock C.EH s.pins) (bh : NIdx) (hB : C.EH[138]? = some (Enc.idxW bh))
    (hbd : denoteN s.store.ns bh = some boolRecName) (hbp : ConRon.Bridge.PersN bh)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1, kBN, kBA, fCap, kZn, fTL, fTE], x ∈ D)
    (hDF : ∀ x ∈ forbidVars, x ∈ D)
    (rb capD jN capM j0 Lw : Nat)
    (hlay : jN + 3 * capM ≤ rb) (hbuf0 : rb + 1 + capD ≤ j0 + 1) (Hb : List (BitVec 64)) (hcells : j0 + Lw ≤ Hb.length)
    (hL16 : 16 ≤ 8 * Lw) (h59 : 8 * Lw < 2 ^ 59)
    (hal : (cellA C j0).toNat % 8 = 0) (hov : (cellA C j0).toNat + 8 * Lw + 8 < 2 ^ 64)
    (hbits : System.Platform.numBits = 64)
    (hcap1 : 1 ≤ capM) (hcapN : capM ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * capM < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64)
    (hZb : Γ.get kZb = some (cellA C jN)) (hTN : Γ.get fTN = some (cellA C jN))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (hRA : Γ.get kRA = some (cellA C j0)) (hRL : Γ.get kRL = some (BitVec.ofNat 64 (8 * Lw)))
    (hRM : Γ.get kRM = some (BitVec.ofNat 64 (8 * Lw - 16)))
    (nb : List (BitVec 8)) (hl : nb.length = 8 * Lw) (hH : C.H = writeH Hb (cellA C j0) j0 0 nb)
    (hbi : ConPanqueque.T.Decl.BasisInv C)
    (t : PState σ) (ht : Inv C s Γ M D t) :
    Stop (evaluateHOLFiniteState t (restP2 capM)).1 ∨
      ((∃ w, (evaluateHOLFiniteState t (restP2 capM)).1 = some (.returned (.val (.word w)))) ∧
        ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
          (∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP rc.decls.toList
            = .ok (ConLeche.streamEnv rc.decls.toList)) ∧
          ∀ d ∈ rc.decls.toList, ∀ n, ConPanqueque.Pipeline.recName d = some n → n ∉ FN) := by
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
  unfold restP2
  rcases T.step_heapLoadI (C := C1) kBN (vv kRA) j0 hj0 (hD _ (by simp)) (by show Γ.get kRA = some (cellA C j0); exact hRA)
      t hinv with
    hs1 | ⟨hn1, hinv1⟩
  · exact Or.inl (seq_stop _ _ _ hs1)
  generalize ht2 : (evaluateHOLFiniteState t (.assign .local kBN (.load .one (vv kRA)))).2 = t2 at hinv1
  have e2 := seq_normal (s := t) (s₁ := t2)
    (.ite (.cmp .lower (vv kBN) (vv kRM)) (.seq (.assign .local kBA (.op .add [vv kRA, .const 8])) (capP capM mainP2)) hang)
    (by rw [← hn1, ← ht2])
  rw [e2]
  let w := C1.H[j0]
  have hw : w = BitVec.ofNat 64 w.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hwv : w.toNat = leNat (nb.take 8) := by
    have := header_value Hb (cellA C j0) j0 hal nb (by omega) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (show j0 < H'.length by omega), Option.getD_some] at this; exact this
  let Γ2 : Env := (kBN, w) :: Γ
  have hg : sev Γ2 (.cmp .lower (vv kBN) (vv kRM)) = some (bw (w.toNat < 8 * Lw - 16)) :=
    sev_lower Γ2 (vv kBN) (vv kRM) w.toNat (8 * Lw - 16) (by simp [Γ2, sev, vv, T.Env.get_cons]) (by
      simp only [sev, vv, Γ2, T.Env.get_cons, ite_eq_right (show kRM ≠ kBN by decide)]; exact hRM) w.isLt (by omega)
  rw [ite_word t2 _ _ _ _ (inv_ev hinv1 hg)]
  by_cases hgd : w.toNat < 8 * Lw - 16
  swap
  · rw [ite_eq_right (by simp [bw, hgd])]; exact Or.inl (stop_hang _)
  rw [ite_eq_left (by simp [bw, hgd])]
  rcases T.step_assignI (C := C1) kBA (.op .add [vv kRA, .const 8]) (cellA C1 (j0 + 1)) (hD _ (by simp)) (by
      simp only [sev, vv, Γ2, T.Env.get_cons, ite_eq_right (show kRA ≠ kBN by decide), hRA, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
      rw [show cellA C1 (j0 + 1) = cellA C j0 + BitVec.ofNat 64 (8 * 1) from cellA_add C j0 1]; rfl) t2 hinv1 with
    hs3 | ⟨hn3, hinv3⟩
  · exact Or.inl (seq_stop _ _ _ hs3)
  generalize ht3 : (evaluateHOLFiniteState t2 (.assign .local kBA (.op .add [vv kRA, .const 8]))).2 = t3 at hinv3
  have e3 := seq_normal (s := t2) (s₁ := t3) (capP capM mainP2) (by rw [← hn3, ← ht3])
  rw [e3]
  -- the parse and the fold
  let b := inputOf nb w.toNat
  have hbsz : b.size = w.toNat := inputOf_size nb _ (by omega)
  have hbuf : BufOK C1 (j0 + 1) b := bufOK_of_read Cp j0 Lw hal hcells (by show (cellA C j0).toNat + 8 * Lw < 2 ^ 64; omega) h59 hbits nb hl _ (by omega)
  let Γ3 : Env := (kBA, cellA C1 (j0 + 1)) :: Γ2
  have g3 : ∀ y, y ≠ kBA → y ≠ kBN → Γ3.get y = Γ.get y := fun y h1 h2 => by
    simp only [Γ3, Γ2, T.Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  -- the id tables' capacity from the input's length
  let c0 := w.toNat / 16 + 2
  let cap := if capM < c0 then capM else c0
  have hw59 : w.toNat < 2 ^ 59 := by omega
  have hcapE : sev Γ3 capE = some (BitVec.ofNat 64 c0) := by
    simp only [capE, sev, vv, Γ3, Γ2, T.Env.get_cons, ite_eq_right (show kBN ≠ kBA by decide), ite_eq_left,
      show (4 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
    congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hcapv : sev Γ3 (.op .add [capE, .panop .mul [.op .sub [.const (BitVec.ofNat 64 capM), capE],
      .cmp .lower (.const (BitVec.ofNat 64 capM)) capE]]) = some (BitVec.ofNat 64 cap) := by
    simp only [sev, hcapE, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    congr 1
    by_cases hlt : capM < c0
    · have : BitVec.ofNat 64 capM < BitVec.ofNat 64 c0 := by rw [BitVec.lt_def]; simp; omega
      simp only [cap, ite_eq_left hlt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true this, ite_true]
      have m1 : ∀ x : BitVec 64, x * 1 = x := fun x => by simp
      rw [m1, BitVec.add_comm, BitVec.sub_add_cancel]
    · have : ¬ BitVec.ofNat 64 capM < BitVec.ofNat 64 c0 := by rw [BitVec.lt_def]; simp; omega
      simp only [cap, ite_eq_right hlt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_false this]
      simp
  have hcap1' : 1 ≤ cap := by simp only [cap]; split <;> omega
  have hcapM : cap ≤ capM := by simp only [cap]; split <;> omega
  rcases T.step_assignI (C := C1) fCap _ (BitVec.ofNat 64 cap) (hD _ (by simp)) hcapv t3 hinv3 with hs5 | ⟨hn5, hinv5⟩
  · exact Or.inl (seq_stop _ _ _ hs5)
  generalize ht5 : (evaluateHOLFiniteState t3 (.assign .local fCap (.op .add [capE, .panop .mul [.op .sub
    [.const (BitVec.ofNat 64 capM), capE], .cmp .lower (.const (BitVec.ofNat 64 capM)) capE]]))).2 = t5 at hinv5
  rw [show capP capM mainP2 = .seq (.assign .local fCap (.op .add [capE, .panop .mul [.op .sub
    [.const (BitVec.ofNat 64 capM), capE], .cmp .lower (.const (BitVec.ofNat 64 capM)) capE]])) _ from rfl,
    seq_normal (s₁ := t5) _ (by rw [← hn5, ← ht5])]
  let Γ5 : Env := (fCap, BitVec.ofNat 64 cap) :: Γ3
  have h3c : 3 * cap < 2 ^ 64 := by omega
  rcases T.step_assignI (C := C1) kZn (.op .add [vv fCap, .op .add [vv fCap, vv fCap]]) (BitVec.ofNat 64 (3 * cap))
      (hD _ (by simp)) (by
        simp only [sev, vv, Γ5, T.Env.get_cons, ite_eq_left, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega) t5 hinv5 with hs6 | ⟨hn6, hinv6⟩
  · exact Or.inl (seq_stop _ _ _ hs6)
  generalize ht6 : (evaluateHOLFiniteState t5 (.assign .local kZn (.op .add [vv fCap, .op .add [vv fCap, vv fCap]]))).2
    = t6 at hinv6
  rw [seq_normal (s₁ := t6) _ (by rw [← hn6, ← ht6])]
  let Γ6 : Env := (kZn, BitVec.ofNat 64 (3 * cap)) :: Γ5
  have hTN6 : Γ6.get fTN = some (cellA C jN) := by
    simp only [Γ6, Γ5, T.Env.get_cons, ite_eq_right (show fTN ≠ kZn by decide), ite_eq_right (show fTN ≠ fCap by decide)]
    rw [g3 _ (by decide) (by decide)]; exact hTN
  have hcl : ∀ k, k ≤ 3 * capM → (cellA C jN + BitVec.ofNat 64 (8 * k)) = cellA C (jN + k) := fun k _ =>
    (cellA_add C jN k).symm
  rcases T.step_assignI (C := C1) fTL (.op .add [vv fTN, .shift .lsl (vv fCap) (.const 3)]) (cellA C (jN + cap))
      (hD _ (by simp)) (by
        simp only [sev, vv, hTN6, Γ6, Γ5, T.Env.get_cons, ite_eq_right (show fCap ≠ kZn by decide), ite_eq_left,
          show (3 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
        rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega), ← hcl cap (by omega)])
      t6 hinv6 with hs7 | ⟨hn7, hinv7⟩
  · exact Or.inl (seq_stop _ _ _ hs7)
  generalize ht7 : (evaluateHOLFiniteState t6 (.assign .local fTL (.op .add [vv fTN, .shift .lsl (vv fCap)
    (.const 3)]))).2 = t7 at hinv7
  rw [seq_normal (s₁ := t7) _ (by rw [← hn7, ← ht7])]
  let Γ7 : Env := (fTL, cellA C (jN + cap)) :: Γ6
  rcases T.step_assignI (C := C1) fTE (.op .add [vv fTL, .shift .lsl (vv fCap) (.const 3)]) (cellA C (jN + 2 * cap))
      (hD _ (by simp)) (by
        simp only [sev, vv, Γ7, Γ6, Γ5, T.Env.get_cons, ite_eq_right (show fCap ≠ kZn by decide),
          ite_eq_right (show fCap ≠ fTL by decide), ite_eq_left,
          show (3 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
        rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega), ← hcl cap (by omega),
          ← hcl (2 * cap) (by omega), BitVec.add_assoc]
        congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega)
      t7 hinv7 with hs8 | ⟨hn8, hinv8⟩
  · exact Or.inl (seq_stop _ _ _ hs8)
  generalize ht8 : (evaluateHOLFiniteState t7 (.assign .local fTE (.op .add [vv fTL, .shift .lsl (vv fCap)
    (.const 3)]))).2 = t8 at hinv8
  rw [seq_normal (s₁ := t8) _ (by rw [← hn8, ← ht8])]
  let Γ8 : Env := (fTE, cellA C (jN + 2 * cap)) :: Γ7
  have g8 : ∀ y, y ≠ fTE → y ≠ fTL → y ≠ kZn → y ≠ fCap → y ≠ kBA → y ≠ kBN → Γ8.get y = Γ.get y :=
    fun y h1 h2 h3 h4 h5 h6 => by
      simp only [Γ8, Γ7, Γ6, Γ5, T.Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]; exact g3 y h5 h6
  rcases front_verdict2 (hbi := hbi) (F := j0 + Lw) (rb := rb) (capD := capD) (jN := jN) (cap := cap) (bufJ := j0 + 1) (b := b)
      pins pinsP ra C1 (ctxOK_ctxH hokp) (frontOK_ctxH (frontOK_H hf Hb)) (frontCodes_ctxH (frontCodes_ctxH fc)) (foldCodes_ctxH (foldCodes_ctxH hc Hb) H') hs hpl hfe hcF
      hEB s hst hoff hpo hpp hpins hA hb bh hB hbd hbp Γ8 [] D (fun x hx => hD x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp)) hDF
      ⟨by omega, by omega, by omega, hbuf0, by rw [hbsz]; omega⟩ hcap1' (by omega) (by omega) hcapD8
      (by show j0 + Lw ≤ H'.length; omega) hbuf
      (by rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hZb)
      (by simp (config := {decide := true}) [Γ8, Γ7, Γ6, T.Env.get_cons])
      (by rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN)
      (by simp (config := {decide := true}) [Γ8, Γ7, T.Env.get_cons]; rfl)
      (by simp (config := {decide := true}) [Γ8, T.Env.get_cons]; rfl)
      (by simp (config := {decide := true}) [Γ8, Γ7, Γ6, Γ5, T.Env.get_cons])
      (by simp (config := {decide := true}) [Γ8, Γ7, Γ6, Γ5, Γ3, T.Env.get_cons])
      (by simp only [Γ8, Γ7, Γ6, Γ5, Γ3, Γ2, T.Env.get_cons, ite_eq_right (show kBN ≠ kBA by decide),
          ite_eq_right (show kBN ≠ fTE by decide), ite_eq_right (show kBN ≠ fTL by decide), ite_eq_right (show kBN ≠ kZn by decide),
          ite_eq_right (show kBN ≠ fCap by decide), ite_eq_left]; rw [hbsz, ← hw])
      (by rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB)
      (by rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hCD)
      (by rw [g8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hZL) t8 hinv8 with hs4 | ⟨hret, rc, hrc, hacc, hnm⟩
  · exact Or.inl hs4
  · refine Or.inr ⟨hret, rc, ?_, hacc, hnm⟩
    rw [← hwv]; exact hrc

end ConPanqueque.Start
