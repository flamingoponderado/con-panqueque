import ConPanqueque.Front.Tags
import ConPanqueque.Scan.ObjInst2

/-! # A payload names its tag

Each payload constructor comes from exactly one `lineTblP` entry, so the scanner's tag word is a
function of con-leche's payload (`plOK_tag_eq`).  Two calls of the line scanner at the same line
then agree: the record is a function of the line (`scanLineFwd`), hence so are the payload and
the tag. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Front

open ConPanqueque.Scan
open ConLeche.Frontend

def plTag : LinePayload → Nat
  | .absent => 0
  | .name (.str _ _) => 5
  | .name (.num _ _) => 6
  | .level (.succ _) => 3
  | .level (.param _) => 4
  | .level (.max _ _) => 18
  | .level (.imax _ _) => 19
  | .expr (.bvar _) => 1
  | .expr (.sort _) => 2
  | .expr (.app _ _) => 7
  | .expr (.lam _ _) => 8
  | .expr (.forallE _ _) => 9
  | .expr (.letE _ _ _) => 10
  | .expr (.const _ _) => 11
  | .expr (.proj _ _ _) => 12
  | .expr (.strVal _) => 13
  | .expr (.natVal _) => 20
  | .decl (.defn _ _ _ _) => 14
  | .decl (.thm _ _) => 15
  | .decl (.opaq _ _ _) => 16
  | .decl (.ax _ _) => 21
  | .decl (.quot _ _) => 22
  | .decl _ => 0
  | .header => 17

theorem srMap_ok {α β : Type} {f : α → β} {x : ScanRes α} {r : β} {e : USize} (h : srMap f x = .ok r e) :
    ∃ a, r = f a := by
  cases x with
  | ok a p => simp only [srMap, ScanRes.ok.injEq] at h; exact ⟨a, h.1.symm⟩
  | err er => simp [srMap] at h

theorem ite_srMap {α β : Type} {c : Bool} {f : α → β} {x : ScanRes α} {er : ScanErr} {r : β} {e : USize}
    (h : (if c = true then srMap f x else .err er) = .ok r e) : ∃ a, r = f a := by
  split at h
  · exact srMap_ok h
  · simp at h


theorem srMap_ite {α β γ : Type} {g : β → γ} {c : Bool} {f : α → β} {x : ScanRes α} {er : ScanErr} {r : γ}
    {e : USize} (h : srMap g (if c = true then srMap f x else .err er) = .ok r e) : ∃ a, r = g (f a) := by
  split at h
  · cases x with
    | ok a p => simp only [srMap, ScanRes.ok.injEq] at h; exact ⟨a, h.1.symm⟩
    | err er => simp [srMap] at h
  · simp [srMap] at h

/-- **The tag word is the payload's tag.** -/
theorem plOK_tag_eq {b : ByteArray} {wpl ws : BitVec 64} {pl : LinePayload} (h : PlOK b wpl ws pl) :
    wpl = BitVec.ofNat 64 (plTag pl) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨k, a, hm, he⟩
  · rfl
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact he.elim
  · exact he.elim
  · exact he.elim
  · obtain ⟨rfl, n, rfl, -⟩ := he; rfl
  · obtain ⟨rfl, n, rfl, -⟩ := he; rfl
  · obtain ⟨rfl, n, rfl, -⟩ := he; rfl
  · obtain ⟨rfl, n, rfl, -⟩ := he; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [nameStr, ConLeche.Frontend.scanStrName] at hs
    rw [scanStrNameLoop_eq b _ (v + 1) true 0 0 "" rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [nameNum, ConLeche.Frontend.scanNumName] at hs
    rw [scanNumNameLoop_eq b _ (v + 1) true 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprApp, ConLeche.Frontend.scanAppExpr] at hs
    rw [scanAppExprLoop_eq b _ (v + 1) true 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprLam, ConLeche.Frontend.scanLamExpr] at hs
    rw [scanLamExprLoop_eq b _ (v + 1) true 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprForall, ConLeche.Frontend.scanForallExpr] at hs
    rw [scanForallExprLoop_eq b _ (v + 1) true 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprLet, ConLeche.Frontend.scanLetExpr] at hs
    rw [scanLetExprLoop_eq b _ (v + 1) true 0 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprConst, ConLeche.Frontend.scanConstExpr] at hs
    rw [scanConstExprLoop_eq b _ (v + 1) true 0 0 [] rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [exprProj, ConLeche.Frontend.scanProjExpr] at hs
    rw [scanProjExprLoop_eq b _ (v + 1) true 0 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, str, rfl, -⟩ := he; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [declDef, ConLeche.Frontend.scanDefDecl] at hs
    rw [scanDefDeclLoop_eq b _ (v + 1) true 0 (.regular 0) [] 0 "" 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [declThm, ConLeche.Frontend.scanThmDecl] at hs
    rw [scanThmDeclLoop_eq b _ (v + 1) true 0 [] 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [declOpaque, ConLeche.Frontend.scanOpaqueDecl] at hs
    rw [scanOpaqueDeclLoop_eq b _ (v + 1) true 0 false [] 0 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [metaHdr] at hs
    split at hs
    · simp at hs
    · split at hs
      · simp at hs
      · simp only [ScanRes.ok.injEq] at hs; rw [← hs.1]; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    obtain ⟨x, y, rfl, -⟩ := levMax_ok hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    obtain ⟨x, y, rfl, -⟩ := levImax_ok hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [natValPl] at hs
    obtain ⟨a, rfl⟩ := srMap_ok hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [declAx, ConLeche.Frontend.scanAxiomDecl] at hs
    rw [scanAxiomDeclLoop_eq b _ (v + 1) true 0 false [] 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl
  · obtain ⟨rfl, v, e, hs, -⟩ := he
    simp only [declQuot, ConLeche.Frontend.scanQuotDecl] at hs
    rw [scanQuotDeclLoop_eq b _ (v + 1) true 0 "" [] 0 0 rfl] at hs
    obtain ⟨a, rfl⟩ := srMap_ite hs; rfl

/-- The payload a record came from. -/
def recPl : LineRec → LinePayload
  | .name _ r => .name r
  | .level _ r => .level r
  | .expr _ r => .expr r
  | .decl d => .decl d
  | .header => .header
  | .blank => .absent

theorem lineEnd_pl {j0 j' : USize} {ik : UInt8} {idx : Nat} {pl : LinePayload} {rec : LineRec}
    (h : lineEnd j0 ik idx pl = .ok rec j') : pl = recPl rec := by
  cases pl <;> simp only [lineEnd] at h
  all_goals first
    | (simp at h; done)
    | (split at h
       · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
       · simp at h)

end ConPanqueque.Front
