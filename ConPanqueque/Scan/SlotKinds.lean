import ConPanqueque.Scan.Obj

/-! # The object loop keeps each slot's kind

Every action writes a fixed kind of value to a fixed slot, so a slot list whose kinds match the
spec keeps them through `objLoop`.  The record readers use this to decode a slot word by the kind
the declaration's builder reads. -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

def SVal.kind : SVal → Nat
  | .n _ => 0
  | .l _ => 1
  | .s _ => 2
  | .b _ => 3
  | .h _ => 4

/-- The slot and kind an action writes. -/
def VAct.wr : VAct → Option (Nat × Nat)
  | .natSet sl => some (sl, 0)
  | .natList sl => some (sl, 1)
  | .str sl => some (sl, 2)
  | .bool sl => some (sl, 3)
  | .hints sl => some (sl, 4)
  | _ => none

def KindsOK (ks : List Nat) (slots : List SVal) : Prop :=
  slots.length = ks.length ∧ ∀ k (hk : k < slots.length), ks[k]? = some slots[k].kind

def SpecKinds (sp : ObjSpec) (ks : List Nat) : Prop :=
  ∀ e ∈ sp.keys, ∀ sl kd, e.2.2.wr = some (sl, kd) → ks[sl]? = some kd

theorem lookupKey_mem {k : Key} : ∀ {ks : List (Key × UInt32 × VAct)} {bit : UInt32} {a : VAct},
    lookupKey k ks = some (bit, a) → (k, bit, a) ∈ ks
  | [], _, _, h => by simp [lookupKey] at h
  | (k', b', a') :: r, bit, a, h => by
    simp only [lookupKey] at h
    split at h
    · rename_i e; subst e; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · exact List.mem_cons_of_mem _ (lookupKey_mem h)

theorem stepVal_kind {b : ByteArray} {i v : USize} {a : VAct} {upd : Option (Nat × SVal)} {e : USize}
    (h : stepVal b i v a = .ok upd e) : upd = none ∨ ∃ sl x, upd = some (sl, x) ∧ a.wr = some (sl, x.kind) := by
  cases a <;> simp only [stepVal] at h
  all_goals first
    | (split at h <;> simp at h; done)
    | (split at h
       · simp at h
       · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h
         first | exact Or.inl rfl | exact Or.inr ⟨_, _, rfl, rfl⟩)
    | (split at h
       · simp at h
       · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; exact Or.inr ⟨_, _, rfl, rfl⟩)

theorem kindsOK_upd {ks : List Nat} {slots : List SVal} (hk : KindsOK ks slots) {a : VAct}
    {upd : Option (Nat × SVal)} (hu : upd = none ∨ ∃ sl x, upd = some (sl, x) ∧ a.wr = some (sl, x.kind))
    (ha : ∀ sl kd, a.wr = some (sl, kd) → ks[sl]? = some kd) : KindsOK ks (applyUpd slots upd) := by
  rcases hu with rfl | ⟨sl, x, rfl, hw⟩
  · exact hk
  · have hks := ha sl x.kind hw
    refine ⟨by simp [applyUpd, hk.1], fun k hk' => ?_⟩
    simp only [applyUpd, List.length_set] at hk' ⊢
    rw [List.getElem_set]
    split
    · rename_i e; subst e; exact hks
    · exact hk.2 k hk'

theorem objLoop_kinds (sp : ObjSpec) (ks : List Nat) (hsp : SpecKinds sp ks) (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (slots : List SVal), b.size - i.toNat = msr →
      KindsOK ks slots → ∀ slots' j, objLoop sp b i wm seen slots = .ok slots' j → KindsOK ks slots' := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i wm seen slots hm hk slots' j h
    rw [objLoop] at h
    split at h
    · rename_i hi
      have h1 := usizeInBounds b i hi
      have h2 := usizeStep b i hi
      simp only at h
      split at h
      · exact ih _ (by omega) _ _ _ _ rfl hk _ _ h
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hk
      split at h
      · split at h
        · simp at h
        · exact ih _ (by omega) _ _ _ _ rfl hk _ _ h
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · rename_i bit a hl
          split at h
          · simp at h
          split at h
          · simp at h
          · rename_i upd e hsv
            split at h
            · rename_i hj
              exact ih _ (by have := USize.lt_iff_toNat_lt.mp hj; omega) _ _ _ _ rfl
                (kindsOK_upd hk (stepVal_kind hsv) (hsp _ (lookupKey_mem hl))) _ _ h
            · simp at h
        · simp at h
      · simp at h
    · simp at h

theorem scanNatListLoop_len (b : ByteArray) :
    ∀ msr (i : USize) (acc : List Nat) (wi : Bool), b.size - i.toNat = msr →
      ∀ us e, scanNatListLoop b i acc wi = .ok us e → us.length ≤ acc.length + (b.size - i.toNat) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i acc wi hm us e h
    rw [scanNatListLoop] at h
    split at h
    · rename_i hi
      have h1 := usizeInBounds b i hi
      have h2 := usizeStep b i hi
      simp only at h
      split at h
      · have := ih _ (by omega) _ _ _ rfl _ _ h; omega
      split at h
      · split at h
        · simp at h
        · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; simp
      split at h
      · split at h
        · simp at h
        · have := ih _ (by omega) _ _ _ rfl _ _ h; omega
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · rename_i hj
          have hj' := USize.lt_iff_toNat_lt.mp hj
          have := ih _ (by omega) _ _ _ rfl _ _ h
          simp only [List.length_cons] at this
          have : (numEnd b i).toNat ≤ b.size ∨ True := Or.inr trivial
          omega
        · simp at h
      · simp at h
    · simp at h

theorem scanNatList_len {b : ByteArray} {p e : USize} {us : List Nat} (h : scanNatList b p = .ok us e) :
    us.length ≤ b.size := by
  rw [scanNatList] at h
  split at h
  · have := scanNatListLoop_len b _ _ [] true rfl _ _ h; simp at this; omega
  · simp at h

end ConPanqueque.Scan
