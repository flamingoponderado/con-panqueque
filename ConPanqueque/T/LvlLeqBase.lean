import ConPanqueque.T.LvlSubst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Level comparison: shared pieces

`Option Bool` answers as words (`none` 0, `some false` 1, `some true` 2) and the integer `diff` as a
signed word (two's complement, kept far from overflow by `|diff| + fuel < 2^62`).
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM

def obW : Option Bool → BitVec 64
  | none => 0
  | some false => 1
  | some true => 2

section
variable {σ : Type}

/-- An `Option Bool`-valued pure function's post (callees may grow the heap: `SR` at `C` survives). -/
def PostOB (C : Ctx) (o : Option Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = obW o ∧ SR C s' st

theorem postOB_locals (C : Ctx) : ∀ (a : Option Bool) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostOB C a w s' st → PostOB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem postOB_weaken {C : Ctx} {H : List (BitVec 64)} (hp : C.H <+: H) {a : Option Bool} {w : BitVec 64}
    {s' : AState} {st : PState σ} (h : PostOB (ctxH C H) a w s' st) : PostOB C a w s' st :=
  ⟨h.1, sr_weakenH h.2 hp⟩

end

/-- The signed word of an integer. -/
def iW (d : Int) : BitVec 64 := BitVec.ofInt 64 d

theorem iW_sub1 (d : Int) : iW d - 1 = iW (d - 1) := by
  unfold iW; apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_sub]

theorem iW_add1 (d : Int) : iW d + 1 = iW (d + 1) := by
  unfold iW; apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_add]

theorem iW_toNat_nonneg (d : Int) (h0 : 0 ≤ d) (h1 : d < 2 ^ 63) : (iW d).toNat = d.toNat := by
  unfold iW
  rw [BitVec.toNat_ofInt]
  have : d % 18446744073709551616 = d := by omega
  simp [this]

theorem iW_toNat_neg (d : Int) (h0 : d < 0) (h1 : -2 ^ 63 ≤ d) : (iW d).toNat = (d + 2 ^ 64).toNat := by
  unfold iW
  rw [BitVec.toNat_ofInt]
  have : d % 18446744073709551616 = d + 18446744073709551616 := by omega
  simp [this]

theorem iW_sign (d : Int) (hl : -2 ^ 63 ≤ d) (hh : d < 2 ^ 63) :
    (iW d >>> (63 : BitVec 64).toNat = 0) ↔ 0 ≤ d := by
  have e : iW d = BitVec.ofNat 64 (iW d).toNat := by simp
  rw [e, shr63_eq_zero _ (iW d).isLt]
  by_cases h0 : 0 ≤ d
  · rw [iW_toNat_nonneg d h0 hh]; omega
  · rw [iW_toNat_neg d (by omega) hl]; omega

end ConPanqueque.T.LLeq
