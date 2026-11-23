import ConPanqueque.T.Decl.EnsureSort
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `constsResolve`: the pinned names a literal needs

A literal's constants resolve when its pinned names (`Nat`, its constructors; for strings also `String`, `List`,
`Char` and theirs) are all in the environment. The port looks them up one by one, answering `false` at the
first missing one.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def crX := ofString "cr_x"
def crY := ofString "cr_y"

/-- Look up the pinned names `is` in turn: `0` at the first missing one, else `1`. -/
def crPins (C : Ctx) : List Nat → ProgHOL 64
  | [] => .return (.const 1)
  | i :: r => .seq (.assign .local crX (.load .one (.const (ecell C (C.PO + i)))))
      (envFindP C crY (vv crX) (.ite (.cmp .equal (vv crY) (.const 0)) (.return (.const 0)) (crPins C r)))

/-- Are the pinned names `is` all in the environment. -/
def pinsFound (C : Ctx) (is : List Nat) : Bool := is.all fun i => (C.fe.find? C.pins.names[i]!).isSome

section
variable {σ : Type}

theorem specR_crPinsI {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {D : List MlS} (hD : crX ∈ D ∧ crY ∈ D) :
    ∀ (is : List Nat) (Γ : Env), (∀ i ∈ is, i < pinCount) → Γ.get lKb = some C.KB →
      SpecR (σ := σ) (Inv C s Γ [] D) (crPins C is) s (pure (pinsFound C is)) (PostB C)
  | [], Γ, _, _ => specR_returnI _ 1 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [pinsFound, boolW],
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | i :: r, Γ, his, hkb => by
    have hi : i < pinCount := his i (by simp)
    have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
    unfold crPins
    refine specR_envLoadI crX _ (C.PO + i) _ hD.1 rfl (hok.pinsRel.2.1 i hi') ?_
    refine specR_envFindI hok hcodeG hcodeP crY (vv crX) C.pins.names[i] hD.2 (by simp [sev, vv]) (by simp [Env.get_cons, hkb]; intro h; exact absurd h (by decide)) ?_
    have hrel := find_rel hok C.pins.names[i]
    have hni : C.pins.names[i]! = C.pins.names[i] := by simp [hi']
    revert hrel
    rcases hf : C.fe.find? C.pins.names[i] with _ | ci
    · intro hrel
      simp only at hrel
      rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      have hfalse : pinsFound C (i :: r) = false := by simp [pinsFound, hni, hf]
      rw [hfalse]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · intro ⟨o, hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      refine specR_ifI _ 0 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
        (fun h => absurd rfl h) (fun _ => ?_)
      have heq : pinsFound C (i :: r) = pinsFound C r := by simp [pinsFound, hni, hf]
      rw [heq]
      exact specR_crPinsI hok hcodeG hcodeP hD r _ (fun j hj => his j (by simp [hj]))
        (by simp [Env.get_cons, hkb]; first | rfl | (intro h; exact absurd h (by decide)) | (rw [if_neg (by decide), if_neg (by decide)]; exact hkb) | (rw [if_neg (by decide)]; first | exact hkb | (rw [if_neg (by decide)]; exact hkb)))

end

end ConPanqueque.T.Decl
