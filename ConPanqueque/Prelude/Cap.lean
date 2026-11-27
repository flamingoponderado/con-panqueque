import ConPanqueque.Prelude.PreParse

/-! # The id tables' capacity from an input length (`capP`), as a specification

`capP_spec`: `capP capM rest` with `kBN = n` runs `rest` with `fCap = cap`, `kZn = 3 cap` and the
three tables at `jN`, `jN + cap`, `jN + 2 cap`, where `cap = min capM (n / 16 + 2)` (the computation
inside `rest_verdict2`, factored out: the program runs it for the stream and for the prelude). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T ConPanqueque.Start

variable {σ : Type}

/-- The capacity `capP` computes. -/
def capOf (capM n : Nat) : Nat := if capM < n / 16 + 2 then capM else n / 16 + 2

theorem capP_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (hD : ∀ x ∈ [fCap, kZn, fTL, fTE], x ∈ D) (capM n jN : Nat) (hn : n < 2 ^ 59) (hcap1 : 1 ≤ capM)
    (hcapM : 8 * (jN + 3 * capM) < 2 ^ 64)
    (hBN : Γ.get kBN = some (BitVec.ofNat 64 n)) (hTN : Γ.get fTN = some (cellA C jN))
    {rest : ProgHOL 64} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ Γ' : Env, (∀ y, y ∉ [fCap, kZn, fTL, fTE] → Γ'.get y = Γ.get y) →
      Γ'.get fCap = some (BitVec.ofNat 64 (capOf capM n)) →
      Γ'.get kZn = some (BitVec.ofNat 64 (3 * capOf capM n)) →
      Γ'.get fTL = some (cellA C (jN + capOf capM n)) →
      Γ'.get fTE = some (cellA C (jN + 2 * capOf capM n)) →
      SpecR (Inv C s Γ' M D) rest s m R) :
    SpecR (Inv C s Γ M D) (capP capM rest) s m R := by
  let c0 := n / 16 + 2
  let cap := if capM < c0 then capM else c0
  have hcapE : sev Γ capE = some (BitVec.ofNat 64 c0) := by
    simp only [capE, sev, vv, hBN, show (4 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hcapv : sev Γ (.op .add [capE, .panop .mul [.op .sub [.const (BitVec.ofNat 64 capM), capE],
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
  have hcapM' : cap ≤ capM := by simp only [cap]; split <;> omega
  unfold capP
  refine specR_assignI fCap _ (BitVec.ofNat 64 cap) (hD _ (by simp)) hcapv ?_
  refine specR_assignI kZn (.op .add [vv fCap, .op .add [vv fCap, vv fCap]]) (BitVec.ofNat 64 (3 * cap))
    (hD _ (by simp)) (by
      simp only [sev, vv, T.Env.get_cons, ite_eq_left, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega) ?_
  have hTN2 : T.Env.get ((kZn, BitVec.ofNat 64 (3 * cap)) :: (fCap, BitVec.ofNat 64 cap) :: Γ) fTN =
      some (cellA C jN) := by
    simp only [T.Env.get_cons, ite_eq_right (show fTN ≠ kZn by decide), ite_eq_right (show fTN ≠ fCap by decide)]
    exact hTN
  have hcl : ∀ k, k ≤ 3 * capM → (cellA C jN + BitVec.ofNat 64 (8 * k)) = cellA C (jN + k) := fun k _ =>
    (cellA_add C jN k).symm
  refine specR_assignI fTL (.op .add [vv fTN, .shift .lsl (vv fCap) (.const 3)]) (cellA C (jN + cap))
      (hD _ (by simp)) (by
        simp only [sev, vv, hTN2, T.Env.get_cons, ite_eq_right (show fCap ≠ kZn by decide), ite_eq_left,
          show (3 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
        rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega), ← hcl cap (by omega)]) ?_
  refine specR_assignI fTE (.op .add [vv fTL, .shift .lsl (vv fCap) (.const 3)]) (cellA C (jN + 2 * cap))
      (hD _ (by simp)) (by
        simp only [sev, vv, T.Env.get_cons, ite_eq_right (show fCap ≠ kZn by decide),
          ite_eq_right (show fCap ≠ fTL by decide), ite_eq_left,
          show (3 : BitVec 64).toNat < 64 by decide, ite_true, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
        rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega), ← hcl cap (by omega),
          ← hcl (2 * cap) (by omega), BitVec.add_assoc]
        congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega) ?_
  refine hk _ (fun y hy => ?_) (by simp (config := {decide := true}) [T.Env.get_cons, cap, capOf, c0])
    (by simp (config := {decide := true}) [T.Env.get_cons, cap, capOf, c0])
    (by simp (config := {decide := true}) [T.Env.get_cons, cap, capOf, c0])
    (by simp (config := {decide := true}) [T.Env.get_cons, cap, capOf, c0])
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp (config := {decide := true}) [T.Env.get_cons, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

end ConPanqueque.Prelude
