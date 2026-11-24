import ConPanqueque.Scan.ObjFun
import ConPanqueque.Scan.ObjInst

/-! # The record functions, per record kind

Each record kind's function `recFun spec inits ret`, specified against con-leche's own record
scanner (`scanAppExpr`, …) through the object-loop instance theorems (`ObjInst`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

section
variable {σ : Type}

theorem retP_mono {t : PanSemStateFiniteExact 64 σ} {c : ProgHOL 64} {P Q : BitVec 64 → Prop}
    (h : RetP t c P) (hpq : ∀ w, P w → Q w) : RetP t c Q := by
  rcases h with hs | ⟨w, r1, hp, r2⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, r1, hpq w hp, r2⟩

/-- The entry of a record function: the declared locals' lookups, from the generic lemma. -/
theorem recEntry_lookup (inits : List (BitVec 64)) (u : PanSemStateFiniteExact 64 σ) (y : MlS) :
    ((recLocals inits).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) u).locals.lookup y =
      match ((recLocals inits).reverse.find? (fun d => d.1 = y)) with
      | some d => some (.val (.word d.2))
      | none => u.locals.lookup y :=
  lookup_foldl_setVar y _ u

/-- **`scanAppExpr` in Pancake (its end) is sound for con-leche's**. -/
theorem appEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun appSpec [0, 0] (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧ j.toNat ≤ b.size + 64 ∧
      ∃ r : ExprRec, scanAppExpr b i = .ok r j) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup [0, 0] t
  have hks : ∀ e ∈ appSpec.keys, ActOK 2 e.2.2 := by
    intro e he; simp only [appSpec, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [ActOK]
  have e := recBody_spec (σ := σ) appSpec 2 t A b hp hb hc hks (by decide) i hi [.n 0, .n 0] rfl sI (Or.inl rfl)
    ((recLocals [0, 0]).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]⟩)
    (by intro k hk; simp only [List.length_cons, List.length_nil] at hk
        refine ⟨0, ?_, ?_⟩
        · rw [hlk]; rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]
        · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp [SlotOK, natCap])
  refine retP_mono e ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ExprRec.app (slots'.getD 1 default).nat (slots'.getD 0 default).nat, ?_⟩
  unfold RecOut at hro
  rw [scanAppExpr, scanAppExprLoop_eq b _ (i + 1) true 0 0 0 rfl]
  split at hro
  · rename_i hbyte; rw [if_pos hbyte, hro]; rfl
  · simp at hro

end

end ConPanqueque.Scan
