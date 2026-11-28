import ConPanqueque.Start.PinPhase
import ConPanqueque.Start.Rest
import ConPanqueque.Code.Top

/-! # The whole program from the harness's start

`mainBody`: declare the locals, store the initial image, read the input, run the pin phase, set
the frontend's locals, then parse and check (`restP`).  This program does not intern the pinned
basis blocks, which the fold's inductive arm needs (`BasisInv`), so its verdict theorem is gone now that
inductive lines are accepted; the definitions here are the later programs' (`Main3`, `Main4`) pieces. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front ConPanqueque.Scan

variable {σ : Type}

set_option maxRecDepth 100000

/-- The concrete code table, at the concrete layout. -/
noncomputable def Cg : Ctx := C1 (codeMap []) [] [] P0
/-- The code table the proofs use (the emitted one, `codeT` in `Start/Main4.lean`, adds `die`). -/
noncomputable def codeTP : Code := codeMap (codeEntries Cg)

theorem codeEntries_C1 (H EH : List (BitVec 64)) (P : Pins) : codeEntries (C1 codeTP H EH P) = codeEntries Cg := rfl

theorem code_C1 (H EH : List (BitVec 64)) (P : Pins) :
    (C1 codeTP H EH P).code = codeMap (codeEntries (C1 codeTP H EH P)) := by rw [codeEntries_C1]; rfl

theorem pinCodes_T : PinCodes codeTP := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [codeTP, codeMap_lookup]; rfl)

/-- Declare each local (initially 0). -/
def decsZ : List MlS → ProgHOL 64 → ProgHOL 64
  | [], body => body
  | x :: xs, body => .dec x .one (.const 0) (decsZ xs body)

theorem decsZ_eval (body : ProgHOL 64) : ∀ (xs : List MlS) (t : PanSemStateFiniteExact 64 σ),
    ∃ (t' : PanSemStateFiniteExact 64 σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
      t'.be = t.be ∧ (∀ x ∈ xs, ∃ w, t'.locals.lookup x = some (.val (.word w))) ∧
      (∀ y, y ∉ xs → t'.locals.lookup y = t.locals.lookup y) ∧
      evaluateHOLFiniteState t (decsZ xs body) =
        ((evaluateHOLFiniteState t' body).1, { (evaluateHOLFiniteState t' body).2 with locals := L })
  | [], t => ⟨t, (evaluateHOLFiniteState t body).2.locals, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by simp),
      fun _ _ => rfl, by simp [decsZ]⟩
  | x :: xs, t => by
    obtain ⟨L1, e1⟩ := dec_word' t x (.const 0) 0 (decsZ xs body) (by simp [evalHOLExact])
    obtain ⟨t', L, h1, h2, h3, h4, h5, h6, h7, e⟩ := decsZ_eval body xs (setVarHOLFinite x (.val (.word 0)) t)
    refine ⟨t', L1, h1, h2, h3, h4, h5, fun y hy => ?_, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · by_cases hyx : y ∈ xs
        · exact h6 y hyx
        · exact ⟨0, by rw [h7 y hyx, lookup_setVar_same]⟩
      · exact h6 y hy
    · simp only [List.mem_cons, not_or] at hy
      rw [h7 y hy.2, lookup_setVar_other _ _ hy.1]
    · simp only [decsZ]; rw [e1, e]

def mainLocals : List MlS :=
  [kZ, kR0, kN0, kR1, kBN, kBA, kZb, kZn, fTN, fTL, fTE, fCap, kRB, kCapD, kZL, kRA, kRL, kRM, vPn, vKa, vPb, vRs]

/-- An empty code map (the program text depends on a context only through its layout). -/
def emptyCode : Code := ⟨fun _ => none, ⟨[], fun _ h => absurd rfl h⟩⟩

/-- The context the program text is generated at. -/
def Cprog : Ctx := Cb emptyCode [] EH0

/-- A value-heap cell's address. -/
def cA (j : Nat) : BitVec 64 := BitVec.ofNat 64 (base + H0) + BitVec.ofNat 64 (8 * j)

theorem cellA_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) (j : Nat) : cellA (C1 code H EH P) j = cA j := rfl
theorem cellA_Cb (code : Code) (H EH : List (BitVec 64)) (j : Nat) : cellA (Cb code H EH) j = cA j := rfl

/-- The frontend's locals: its three tables, the registry, the zero level, the length bound. -/
def frontAssigns (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kZb (.const (cA 0)))
  (.seq (.assign .local kZn (.const (BitVec.ofNat 64 (3 * capF))))
  (.seq (.assign .local fTN (.const (cA 0)))
  (.seq (.assign .local fTL (.const (cA capF)))
  (.seq (.assign .local fTE (.const (cA (2 * capF))))
  (.seq (.assign .local fCap (.const (BitVec.ofNat 64 capF)))
  (.seq (.assign .local kRB (.const (cA rbF)))
  (.seq (.assign .local kCapD (.const (BitVec.ofNat 64 capD)))
  (.seq (.assign .local kZL (.const 0))
  (.seq (.assign .local kRM (.const (BitVec.ofNat 64 (8 * Lw - 16))))
    rest)))))))))

/-- The body after the declarations. -/
def mainCore : ProgHOL 64 :=
  .seq (storesP initL)
  (.seq (.assign .local kRA (.const (cA j0F)))
  (.seq (.assign .local kRL (.const (BitVec.ofNat 64 (8 * Lw))))
  (.seq (.extCall fRead (.const 0) (.const 0) (vv kRA) (vv kRL))
    (pinsP Cprog (frontAssigns restP)))))

def mainBody : ProgHOL 64 := decsZ mainLocals mainCore

theorem pinsP_Cb (code code' : Code) (H EH H' EH' : List (BitVec 64)) (r : ProgHOL 64) :
    pinsP (Cb code H EH) r = pinsP (Cb code' H' EH') r := by
  unfold pinsP
  have eA := envAllocP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  have eN := namesP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  have eL := allocP_congr (C := Cb code H EH) (C' := Cb code' H' EH') rfl rfl
  rw [eA, eA, eN, eN, eL]

theorem initL_dom : ∀ p ∈ initL, p.1.toNat % 8 = 0 ∧ base ≤ p.1.toNat ∧ p.1.toNat < base + SZ := by
  decide +kernel

/-- The verdict the program's return carries. -/
def Verdict (nb : List (BitVec 8)) : Prop :=
  ∃ rc, ConLeche.Frontend.parseBytes (inputOf nb (leNat (nb.take 8))) = .ok rc ∧
    ∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') [] rc.decls.toList
      = .ok (ConLeche.streamEnv rc.decls.toList)

end ConPanqueque.Start
