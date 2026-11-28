import ConPanqueque.T.Ind.ClassCtor

/-!
# Decoding a recursive field's kinds word, and a block of class records

`cfKindW (.recursive c tele) = (tele + 1) + 2 ^ 32 * c`: the class is the word shifted right by `32`, the telescope
the low `32` bits minus one.  `TMBlkR`: a block of target-major records with no condition on their `nfs`/`pfvs`
(the generator's classes carry their filtered tables, `TMBlk` asks for none).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T

theorem kindW_cls (c tele : Nat) (ht : tele + 1 < 2 ^ 32) (hc : c < 2 ^ 24) :
    BitVec.ofNat 64 (tele + 1 + 2 ^ 32 * c) >>> (32 : Nat) = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem kindW_tele (c tele : Nat) (ht : tele + 1 < 2 ^ 32) (hc : c < 2 ^ 24) :
    (BitVec.ofNat 64 (tele + 1 + 2 ^ 32 * c) &&& BitVec.ofNat 64 (2 ^ 32 - 1)) - 1#64 = BitVec.ofNat 64 tele := by
  have e : BitVec.ofNat 64 (tele + 1 + 2 ^ 32 * c) &&& BitVec.ofNat 64 (2 ^ 32 - 1) = BitVec.ofNat 64 (tele + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e]; exact ConPanqueque.T.Ex.ofNat_succ_sub_one tele

/-- A block of target-major records (no condition on their tables or openers). -/
def TMBlkR (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ms : List TargetMajor) : Prop :=
  ∃ ps : List Nat, ps.length = ms.length ∧ BlkAt H o (ps.map (cellA C)) ∧
    ∀ k (hk : k < ms.length), ∃ op, ps[k]? = some op ∧ TMRep C H op ms[k]

theorem tmBlkR_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {ms : List TargetMajor}
    (h : TMBlkR C H o ms) : TMBlkR C H' o ms :=
  let ⟨ps, hl, hb, hr⟩ := h
  ⟨ps, hl, blkAt_mono hb hp, fun k hk => let ⟨op, h1, h2⟩ := hr k hk; ⟨op, h1, tmRep_mono hp h2⟩⟩

theorem tmBlkR_of_tmBlk {C : Ctx} {H : List (BitVec 64)} {o : Nat} {pfvs : List EIdx} {ms : List TargetMajor}
    (h : TMBlk C H o pfvs ms) : TMBlkR C H o ms :=
  let ⟨ps, hl, hb, hr⟩ := h
  ⟨ps, hl, hb, fun k hk => let ⟨op, h1, h2, _⟩ := hr k hk; ⟨op, h1, h2⟩⟩

/-- Changing every record's table keeps the block. -/
theorem tmBlkR_nfs {C : Ctx} {H : List (BitVec 64)} {o : Nat} {ms : List TargetMajor}
    (g : TargetMajor → List NestCtorNf) (h : TMBlkR C H o ms) :
    TMBlkR C H o (ms.map (fun m => { m with nfs := g m })) := by
  obtain ⟨ps, hl, hb, hr⟩ := h
  refine ⟨ps, by simp [hl], hb, fun k hk => ?_⟩
  simp only [List.length_map] at hk
  obtain ⟨op, h1, h2⟩ := hr k hk
  rw [List.getElem_map]; exact ⟨op, h1, h2⟩

end ConPanqueque.T.Ind
