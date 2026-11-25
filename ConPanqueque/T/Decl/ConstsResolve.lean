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

def crH := ofString "cr_h"
def natPins : List Nat := [PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC]
def strPins : List Nat := [PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST,
  PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT]
def crLocals : List MlS := [crX, crY, lFl, lDh, lDt, lDg, lDi, lRp, lRn]

/-- `constsResolve` at a leaf (`bvar`, `sort`, `const`, `lit`): the constant's or the literal's pinned names. -/
def crLeafBody (C : Ctx) : ProgHOL 64 := prologue crLocals
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv crH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local crX (.load .one (vv lRp)))
      (envFindP C crY (vv crX) (.ite (.cmp .equal (vv crY) (.const 0)) (.return (.const 0)) (.return (.const 1)))))
  (.ite (.cmp .equal (vv lDg) (.const 8))
    (.seq (.assign .local crX (.load .one (vv lRp)))
      (.ite (.cmp .equal (vv crX) (.const 0)) (crPins C natPins) (crPins C strPins)))
    (.return (.const 1)))))))

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
        (by simp [Env.get_cons, hkb]; first | rfl | (intro h; exact absurd h (by decide)) | (rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact hkb) | (rw [ite_eq_right (by decide)]; first | exact hkb | (rw [ite_eq_right (by decide)]; exact hkb)))


theorem pinAt_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (i : Nat) (hi : i < pinCount) :
    pinAt i s = .ok (C.pins.names[i]!, s) := by
  have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
  simp [pinAt, hp, hi', get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure]


theorem natLit_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    (do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      pure ((C.fe.find? nt).isSome && (C.fe.find? nz).isSome && (C.fe.find? ns).isSome) : AM Bool) s =
    (pure (pinsFound C natPins) : AM Bool) s := by
  simp only [pinNat, pinNatZero, pinNatSucc, bind, StateT.bind, Except.bind, pinAt_run hok hp PIN_NAT (by decide), pinAt_run hok hp PIN_NAT_ZERO (by decide), pinAt_run hok hp PIN_NAT_SUCC (by decide)]
  simp [pinsFound, natPins, pure, StateT.pure, Bool.and_assoc]

theorem strLit_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    (do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      let st ← pinString
      let sl ← pinStringOfList
      let li ← pinList
      let ln ← pinListNil
      let lc ← pinListCons
      let ch ← pinChar
      let co ← pinCharOfNat
      pure ((C.fe.find? nt).isSome && (C.fe.find? nz).isSome &&
        (C.fe.find? ns).isSome && (C.fe.find? st).isSome &&
        (C.fe.find? sl).isSome && (C.fe.find? li).isSome &&
        (C.fe.find? ln).isSome && (C.fe.find? lc).isSome &&
        (C.fe.find? ch).isSome && (C.fe.find? co).isSome) : AM Bool) s =
    (pure (pinsFound C strPins) : AM Bool) s := by
  simp only [pinNat, pinNatZero, pinNatSucc, pinString, pinStringOfList, pinList, pinListNil, pinListCons, pinChar,
    pinCharOfNat, bind, StateT.bind, Except.bind, pinAt_run hok hp PIN_NAT (by decide), pinAt_run hok hp PIN_NAT_ZERO (by decide), pinAt_run hok hp PIN_NAT_SUCC (by decide), pinAt_run hok hp PIN_STRING (by decide), pinAt_run hok hp PIN_STRING_OF_LIST (by decide), pinAt_run hok hp PIN_LIST (by decide), pinAt_run hok hp PIN_LIST_NIL (by decide), pinAt_run hok hp PIN_LIST_CONS (by decide), pinAt_run hok hp PIN_CHAR (by decide), pinAt_run hok hp PIN_CHAR_OF_NAT (by decide)]
  simp [pinsFound, strPins, pure, StateT.pure, Bool.and_assoc]


theorem cr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crLocals → (ctxEnv C ++ [crH].zip vals).get x = none :=
  Knot.params_none C crLocals [crH] vals (by decide) (by decide)

theorem crw_succ : ∃ k, coreWalkFuel = k + 1 := ⟨coreWalkFuel - 1, by unfold coreWalkFuel; omega⟩

/-- **`constsResolve` at a leaf**. -/
theorem cr_leaf_spec (C : Ctx) (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (h : EIdx)
    (hleaf : ∀ v, s.store.view h = some v → v.tagN = 0 ∨ v.tagN = 2 ∨ v.tagN = 3 ∨ v.tagN = 8) :
    SpecR (σ := σ) (Pre C s ([crH].zip [Enc.idxW h])) (crLeafBody C) s (constsResolve C.fe coreWalkFuel h) (PostB C) := by
  refine specR_prologue (postB_locals C) (cr_none C _) ?_
  obtain ⟨k, hk⟩ := crw_succ
  rw [hk, constsResolve]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv crH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by decide) (fun v P hv htn _ => ?_)
  refine specR_congr (view_bind_eq h v _ s hv) ?_
  have hl := hleaf v hv
  have hret1 : ∀ {Γ : Env} {M : Mem} {D : List MlS}, SpecR (σ := σ) (Inv C s Γ M D) (.return (.const 1)) s (pure true)
      (PostB C) := fun {Γ M D} =>
    specR_returnI _ 1 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rcases v with i | ⟨idx, ty⟩ | u | ⟨c, us⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨sn, i, pe⟩
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret1
  · simp [ENodeView.tagN] at hl
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret1
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' crX (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_envFindI hok hcodeG hcodeP crY (vv crX) c (by decide) (by simp [sev, vv])
      (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := find_rel hok c
    revert hrel
    rcases hf : C.fe.find? c with _ | ci
    · intro hrel
      simp only at hrel
      rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [boolW, hf], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · intro ⟨o, hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      refine specR_ifI _ 0 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ 1 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [boolW, hf], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · simp [ENodeView.tagN] at hl
  · simp [ENodeView.tagN] at hl
  · simp [ENodeView.tagN] at hl
  · simp [ENodeView.tagN] at hl
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_atEntry fun t ht => ?_
    have hp := ht.sr.pins
    rcases l with n | str
    · refine specR_loadI' crX (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (Enc.limbs n) []) ?_
      refine specR_ifI _ 1 (by simp [sev, vv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_congr (natLit_run hok hp) ?_
      refine specR_dropM ?_
      exact specR_crPinsI hok hcodeG hcodeP ⟨by decide, by decide⟩ natPins _ (by decide)
        (by simp +decide [Env.get, ctxEnv] <;> rfl)
    · refine specR_loadI' crX (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (Enc.strW str) []) ?_
      refine specR_ifI _ 0 (by simp [sev, vv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_congr (strLit_run hok hp) ?_
      refine specR_dropM ?_
      exact specR_crPinsI hok hcodeG hcodeP ⟨by decide, by decide⟩ strPins _ (by decide)
        (by simp +decide [Env.get, ctxEnv] <;> rfl)
  · simp [ENodeView.tagN] at hl

end

end ConPanqueque.T.Decl
