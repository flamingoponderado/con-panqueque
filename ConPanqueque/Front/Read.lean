import ConPanqueque.Front.ReadMem

/-! # The input read: one external call fills heap cells

`specR_readI`: `extCall f 0 0 kRA kRL` with `kRA = cellA C j0` and `kRL = 8·Lw` either ends in an FFI
event (a stop) or returns `8·Lw` bytes `nb` from the oracle, written into cells `j0 …`
(`writeH`); the continuation runs at that image, for every such `nb`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

def kRA := ofString "kra"
def kRL := ofString "krl"

theorem readBA_isSome (getByte : BitVec 64 → Option (BitVec 8)) :
    ∀ (n : Nat) (a : BitVec 64), (∀ i, i < n → (getByte (a + BitVec.ofNat 64 i)).isSome) →
      (readBytearrayWordHOL (byteWidth := 8) a n getByte).isSome
  | 0, a, _ => by simp [readBytearrayWordHOL]
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h0
    have ih := readBA_isSome getByte n (a + 1) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [BitVec.add_assoc, show (1 : BitVec 64) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64, Nat.add_comm]])
    obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp ih
    simp only [readBytearrayWordHOL, hx]; rw [hys]; rfl

theorem callFFI_ret_length {st : HolFfiState σ} {nm : HolFfiName} {c bs : List (BitVec 8)} {st' : HolFfiState σ}
    {nb : List (BitVec 8)} (h : callFFIHOL st nm c bs = .ret st' nb) : nb.length = bs.length := by
  unfold callFFIHOL at h
  split at h
  · simp only [HolFfiResult.ret.injEq] at h; rw [← h.2]
  · split at h
    · split at h
      · simp only [HolFfiResult.ret.injEq] at h; rw [← h.2]; assumption
      · cases h
    · cases h

theorem readBA_length (getByte : BitVec 64 → Option (BitVec 8)) :
    ∀ (n : Nat) (a : BitVec 64) (bs : List (BitVec 8)), readBytearrayWordHOL (byteWidth := 8) a n getByte = some bs →
      bs.length = n
  | 0, a, bs, h => by simp [readBytearrayWordHOL] at h; subst h; rfl
  | n + 1, a, bs, h => by
    unfold readBytearrayWordHOL at h
    simp only [bind, Option.bind, pure] at h
    split at h
    · cases h
    · simp only at h
      split at h
      · cases h
      · rename_i ys hys; cases h; simp [readBA_length getByte n _ ys hys]

/-- **The read.** -/
theorem specR_readI {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (j0 Lw : Nat) (f : MlS)
    (hal : (cellA C j0).toNat % 8 = 0) (hcells : j0 + Lw ≤ C.H.length) (hov : (cellA C j0).toNat + 8 * Lw < 2 ^ 64)
    (hRA : Γ.get kRA = some (cellA C j0)) (hRL : Γ.get kRL = some (BitVec.ofNat 64 (8 * Lw)))
    (hk : ∀ nb : List (BitVec 8), nb.length = 8 * Lw →
      SpecR (Inv (ctxH C (writeH C.H (cellA C j0) j0 0 nb)) s Γ [] D) rest s m R) :
    SpecR (fun t => Inv (σ := σ) C s Γ M D t ∧ t.be = false)
      (.seq (.extCall f (.const 0) (.const 0) (vv kRA) (vv kRL)) rest) s m R := by
  refine specR_step (Q := fun t' => ∃ nb : List (BitVec 8), nb.length = 8 * Lw ∧
    Inv (ctxH C (writeH C.H (cellA C j0) j0 0 nb)) s Γ [] D t') ?_ (fun t ⟨nb, hl, ht⟩ => hk nb hl t ht)
  intro t ⟨ht, hbe⟩
  rw [evaluateHOLFiniteState_extCall_source]
  have e1 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := by simp only [evalHOLFinite]; exact inv_ev ht rfl
  have e3 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (vv kRA) =
      some (.val (.word (cellA C j0))) := by simp only [evalHOLFinite]; exact inv_ev ht (by simpa [sev, vv] using hRA)
  have e4 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (vv kRL) =
      some (.val (.word (BitVec.ofNat 64 (8 * Lw)))) := by
    simp only [evalHOLFinite]; exact inv_ev ht (by simpa [sev, vv] using hRL)
  rw [e1, e3, e4]
  simp only
  have hL : (BitVec.ofNat 64 (8 * Lw)).toNat = 8 * Lw := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hload : ∀ i, i < 8 * Lw → (@panMemLoadByteWord8HOL 64 _ t.memory t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.be (cellA C j0 + BitVec.ofNat 64 i)).isSome := by
    intro i hi
    have hc := heap_cell ht.sr (j0 + i / 8) (by omega)
    have hal' : panByteAlignHOL (cellA C j0 + BitVec.ofNat 64 i) = cellA C (j0 + i / 8) := by
      rw [align_cell _ _ hal (by omega), cellA_add]
    unfold panMemLoadByteWord8HOL
    simp only [hal', hc.2]
    rw [if_pos (by rw [hal']; exact hc.1)]; rfl
  obtain ⟨bs2, hbs2⟩ := Option.isSome_iff_exists.mp
    (readBA_isSome _ (8 * Lw) (cellA C j0) hload)
  have hbl := readBA_length _ _ _ _ hbs2
  have h0 : ∀ g, readBytearrayWordHOL (byteWidth := 8) (0 : BitVec 64) (BitVec.toNat (0 : BitVec 64)) g = some [] :=
    fun g => rfl
  rw [hL, hbs2, h0]
  simp only
  cases hffi : callFFIHOL t.ffi (.extCall f) [] bs2 with
  | final ev => simp only; exact Or.inl (Or.inr ⟨ev, rfl⟩)
  | ret ffi' nb =>
    simp only
    have hnl : nb.length = 8 * Lw := by rw [callFFI_ret_length hffi, hbl]
    refine Or.inr ⟨trivial, nb, hnl, ?_, fun x v hx => ht.env x v hx, fun _ _ h => absurd h (by simp), fun x hx => ht.decl x hx⟩
    have hw := sr_write (σ := σ) hok j0 hal nb 0 t (inst := fun a => Classical.propDecidable (t.memaddrs a)) ht.sr
      (by omega) (by omega)
    rw [BitVec.add_zero] at hw
    refine sr_of_eq hw ?_ rfl rfl rfl
    show (@panWriteBytearrayWord8HOL 64 _ (cellA C j0) nb t.memory t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.be) = _
    rw [hbe]

/-- The read as a step, with the FFI event it records. -/
theorem read_step
    (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (j0 Lw : Nat) (f : MlS)
    (hal : (cellA C j0).toNat % 8 = 0) (hcells : j0 + Lw ≤ C.H.length) (hov : (cellA C j0).toNat + 8 * Lw < 2 ^ 64)
    (hRA : Γ.get kRA = some (cellA C j0)) (hRL : Γ.get kRL = some (BitVec.ofNat 64 (8 * Lw)))
    (hf : f ≠ MlString.implode []) (t : PState σ) (ht : Inv C s Γ M D t) (hbe : t.be = false) :
    Stop (evaluateHOLFiniteState t (.extCall f (.const 0) (.const 0) (vv kRA) (vv kRL))).1 ∨
      ((evaluateHOLFiniteState t (.extCall f (.const 0) (.const 0) (vv kRA) (vv kRL))).1 = none ∧
        ∃ (nb bs : List (BitVec 8)), nb.length = 8 * Lw ∧
          (evaluateHOLFiniteState t (.extCall f (.const 0) (.const 0) (vv kRA) (vv kRL))).2.ffi.ioEvents =
            t.ffi.ioEvents ++ [⟨.extCall f, [], bs.zip nb⟩] ∧
          Inv (ctxH C (writeH C.H (cellA C j0) j0 0 nb)) s Γ [] D
            (evaluateHOLFiniteState t (.extCall f (.const 0) (.const 0) (vv kRA) (vv kRL))).2) := by
  rw [evaluateHOLFiniteState_extCall_source]
  have e1 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := by simp only [evalHOLFinite]; exact inv_ev ht rfl
  have e3 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (vv kRA) =
      some (.val (.word (cellA C j0))) := by simp only [evalHOLFinite]; exact inv_ev ht (by simpa [sev, vv] using hRA)
  have e4 : @evalHOLFinite 64 σ _ t (fun a => Classical.propDecidable (t.memaddrs a)) (vv kRL) =
      some (.val (.word (BitVec.ofNat 64 (8 * Lw)))) := by
    simp only [evalHOLFinite]; exact inv_ev ht (by simpa [sev, vv] using hRL)
  rw [e1, e3, e4]
  simp only
  have hL : (BitVec.ofNat 64 (8 * Lw)).toNat = 8 * Lw := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hload : ∀ i, i < 8 * Lw → (@panMemLoadByteWord8HOL 64 _ t.memory t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.be (cellA C j0 + BitVec.ofNat 64 i)).isSome := by
    intro i hi
    have hc := heap_cell ht.sr (j0 + i / 8) (by omega)
    have hal' : panByteAlignHOL (cellA C j0 + BitVec.ofNat 64 i) = cellA C (j0 + i / 8) := by
      rw [align_cell _ _ hal (by omega), cellA_add]
    unfold panMemLoadByteWord8HOL
    simp only [hal', hc.2]
    rw [if_pos (by rw [hal']; exact hc.1)]; rfl
  obtain ⟨bs2, hbs2⟩ := Option.isSome_iff_exists.mp
    (readBA_isSome _ (8 * Lw) (cellA C j0) hload)
  have hbl := readBA_length _ _ _ _ hbs2
  have h0 : ∀ g, readBytearrayWordHOL (byteWidth := 8) (0 : BitVec 64) (BitVec.toNat (0 : BitVec 64)) g = some [] :=
    fun g => rfl
  rw [hL, hbs2, h0]
  simp only
  cases hffi : callFFIHOL t.ffi (.extCall f) [] bs2 with
  | final ev => simp only; exact Or.inl (Or.inr ⟨ev, rfl⟩)
  | ret ffi' nb =>
    simp only
    have hnl : nb.length = 8 * Lw := by rw [callFFI_ret_length hffi, hbl]
    refine Or.inr ⟨trivial, nb, bs2, hnl, ?_, ?_, fun x v hx => ht.env x v hx, fun _ _ h => absurd h (by simp),
      fun x hx => ht.decl x hx⟩
    · show ffi'.ioEvents = _
      unfold callFFIHOL at hffi
      rw [if_neg (by intro h; exact hf (HolFfiName.extCall.inj h))] at hffi
      split at hffi
      · split at hffi
        · simp only [HolFfiResult.ret.injEq] at hffi; rw [← hffi.1, ← hffi.2]
        · cases hffi
      · cases hffi
    have hw := sr_write (σ := σ) hok j0 hal nb 0 t (inst := fun a => Classical.propDecidable (t.memaddrs a)) ht.sr
      (by omega) (by omega)
    rw [BitVec.add_zero] at hw
    refine sr_of_eq hw ?_ rfl rfl rfl
    show (@panWriteBytearrayWord8HOL 64 _ (cellA C j0) nb t.memory t.memaddrs
      (fun a => Classical.propDecidable (t.memaddrs a)) t.be) = _
    rw [hbe]

end ConPanqueque.Front
