/-!
# The cons table, as a pure model

An open-addressed table with linear probing over `n` slots: slot `j` holds `0`
(empty) or `i + 1`, naming row `i` of a row list `rows` (the node records; the
key of a slot is the row it names, as in con-ron's key-free `cons_map`). The
invariant `Inv` says every row is reachable from its key's home slot without
crossing an empty slot, slots name distinct rows, and rows are distinct.
`probe_correct`: the probe loop finds the row equal to a key exactly when there
is one. This is what makes the Pancake table an exact refinement of the twin's
`Std.HashMap` cons table.
-/

namespace ConPanqueque.ConsModel

variable {α : Type} [DecidableEq α]

/-- The probe loop: from slot `j`, at most `fuel` steps. -/
def probe (rows : List α) (slots : List Nat) (n : Nat) (a : α) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j =>
    match slots[j]? with
    | none => none
    | some 0 => none
    | some (i + 1) => if rows[i]? = some a then some i else probe rows slots n a fuel ((j + 1) % n)

/-- Slot `(h + d) % n`, the `d`-th slot of the probe path from `h`. -/
def at_ (n h d : Nat) : Nat := (h + d) % n

structure Inv (home : α → Nat) (rows : List α) (slots : List Nat) (n : Nat) : Prop where
  len : slots.length = n
  pos : 0 < n
  home_lt : ∀ a, home a < n
  named : ∀ (j i : Nat), slots[j]? = some (i + 1) → i < rows.length
  /-- Every row sits `d < n` steps along its key's probe path, with no empty slot before it. -/
  reach : ∀ i (hi : i < rows.length), ∃ d, d < n ∧
    slots[at_ n (home (rows[i])) d]? = some (i + 1) ∧
    ∀ d', d' < d → slots[at_ n (home (rows[i])) d']? ≠ some 0
  rows_nodup : rows.Nodup

/-- A hit names a row equal to the key. -/
theorem probe_some (rows : List α) (slots : List Nat) (n : Nat) (a : α) :
    ∀ fuel j i, probe rows slots n a fuel j = some i → rows[i]? = some a
  | 0, _, _, h => by simp [probe] at h
  | fuel + 1, j, i, h => by
    simp only [probe] at h
    split at h
    · cases h
    · cases h
    · rename_i k _
      split at h
      · rename_i hr; cases h; exact hr
      · exact probe_some rows slots n a fuel _ i h

/-- Along a probe path with no empty slot before offset `d`, where row `i`'s slot is, the loop
started at offset `k ≤ d` with enough fuel hits. -/
theorem probe_hits (home : α → Nat) (rows : List α) (slots : List Nat) (n : Nat) (a : α) (i d : Nat)
    (hpos : 0 < n) (hrow : rows[i]? = some a) (hd : slots[at_ n (home a) d]? = some (i + 1))
    (hne : ∀ d', d' < d → slots[at_ n (home a) d']? ≠ some 0)
    (hfull : ∀ d', d' ≤ d → (slots[at_ n (home a) d']?).isSome) :
    ∀ m k, k + m = d → ∀ fuel, m < fuel → (probe rows slots n a fuel (at_ n (home a) k)).isSome := by
  intro m
  induction m with
  | zero =>
    intro k hk fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    subst hk
    simp only [Nat.add_zero] at hd hne
    simp [probe, hd, hrow]
  | succ m ih =>
    intro k hk fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hs := hfull k (by omega)
    have hn0 := hne k (by omega)
    simp only [probe]
    cases e : slots[at_ n (home a) k]? with
    | none => rw [e] at hs; simp at hs
    | some v =>
      cases v with
      | zero => rw [e] at hn0; exact absurd rfl hn0
      | succ j =>
        simp only
        split
        · simp
        · have : (at_ n (home a) k + 1) % n = at_ n (home a) (k + 1) := by
            simp only [at_]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
          rw [this]
          exact ih (k + 1) (by omega) f (by omega)

/-- The probe loop from `home a` with fuel `n` hits exactly when `a` is a row, and then names it. -/
theorem probe_correct (home : α → Nat) (rows : List α) (slots : List Nat) (n : Nat)
    (hinv : Inv (α := α) home rows slots n) (a : α) :
    (∀ i, probe rows slots n a n (home a) = some i → rows[i]? = some a) ∧
    (probe rows slots n a n (home a) = none ↔ a ∉ rows) := by
  refine ⟨probe_some rows slots n a n (home a), ?_⟩
  constructor
  · intro hnone hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨d, hdn, hd, hne⟩ := hinv.reach i hi
    have hfull : ∀ d', d' ≤ d → (slots[at_ n (home rows[i]) d']?).isSome := by
      intro d' _
      have : at_ n (home rows[i]) d' < slots.length := by rw [hinv.len]; exact Nat.mod_lt _ hinv.pos
      simp [this]
    have := probe_hits home rows slots n rows[i] i d hinv.pos (by simp [hi]) hd hne hfull d 0 (by omega) n hdn
    have h0 : at_ n (home rows[i]) 0 = home rows[i] := by simp [at_, Nat.mod_eq_of_lt (hinv.home_lt _)]
    rw [h0, hnone] at this; simp at this
  · intro hmem
    cases e : probe rows slots n a n (home a) with
    | none => rfl
    | some i =>
      have := probe_some rows slots n a n (home a) i e
      exact absurd (List.mem_of_getElem? this) hmem

end ConPanqueque.ConsModel
