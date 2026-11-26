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
  /-- A row is named by one slot only. -/
  uniq : ∀ (j j' i : Nat), slots[j]? = some (i + 1) → slots[j']? = some (i + 1) → j = j'
  /-- Along a row's probe path, every slot before its own names an earlier row (insertion order). -/
  ord : ∀ i (hi : i < rows.length) dd d k, dd < n → slots[at_ n (home rows[i]) dd]? = some (i + 1) → d < dd →
    slots[at_ n (home rows[i]) d]? = some (k + 1) → k < i

theorem at_inj {n h a b : Nat} (ha : a < n) (hb : b < n) (e : at_ n h a = at_ n h b) : a = b := by
  unfold at_ at e
  rcases Nat.lt_or_ge a b with hab | hab
  · have h1 : n ∣ (h + b) - (h + a) := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e.symm)
    have h2 : (h + b) - (h + a) = b - a := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1; omega
  · rcases Nat.eq_or_lt_of_le hab with e2 | hab
    · exact e2.symm
    · have h1 : n ∣ (h + a) - (h + b) := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e)
      have h2 : (h + a) - (h + b) = a - b := by omega
      rw [h2] at h1
      have := Nat.le_of_dvd (by omega) h1; omega

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

/-- The first offset `d ≥ k` (below `n`) on the probe path from `h` whose slot is empty. -/
def firstEmpty (slots : List Nat) (n h : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k => if slots[at_ n h k]? = some 0 then some k else firstEmpty slots n h fuel (k + 1)

theorem firstEmpty_spec (slots : List Nat) (n h : Nat) :
    ∀ fuel k d, firstEmpty slots n h fuel k = some d →
      k ≤ d ∧ d < k + fuel ∧ slots[at_ n h d]? = some 0 ∧ ∀ d', k ≤ d' → d' < d → slots[at_ n h d']? ≠ some 0
  | 0, _, _, e => by simp [firstEmpty] at e
  | fuel + 1, k, d, e => by
    simp only [firstEmpty] at e
    split at e
    · rename_i h0; cases e; exact ⟨Nat.le_refl _, by omega, h0, fun d' h1 h2 => by omega⟩
    · rename_i h0
      obtain ⟨a1, a2, a3, a4⟩ := firstEmpty_spec slots n h fuel (k + 1) d e
      refine ⟨by omega, by omega, a3, fun d' h1 h2 => ?_⟩
      by_cases hk : d' = k
      · subst hk; exact h0
      · exact a4 d' (by omega) h2

/-- Inserting a key that is not a row, at the first empty slot of its probe path, keeps `Inv`. -/
theorem insert_inv (home : α → Nat) (rows : List α) (slots : List Nat) (n : Nat)
    (hinv : Inv (α := α) home rows slots n) (a : α) (ha : a ∉ rows) (d : Nat)
    (hd : firstEmpty slots n (home a) n 0 = some d) :
    Inv (α := α) home (rows ++ [a]) (slots.set (at_ n (home a) d) (rows.length + 1)) n := by
  obtain ⟨-, hdn, hd0, hprev⟩ := firstEmpty_spec slots n (home a) n 0 d hd
  simp only [Nat.zero_add] at hdn
  generalize hj : at_ n (home a) d = j at hd0 ⊢
  have hjlt : j < slots.length := by rw [hinv.len, ← hj]; exact Nat.mod_lt _ hinv.pos
  -- slot lookups after the set
  have get_set : ∀ x, (slots.set j (rows.length + 1))[x]? = if j = x then some (rows.length + 1) else slots[x]? := by
    intro x; rw [List.getElem?_set]; by_cases e : j = x
    · subst e; simp [hjlt]
    · simp [e]
  refine ⟨by simp [hinv.len], hinv.pos, hinv.home_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro x i hx
    rw [get_set] at hx
    split at hx
    · cases hx; simp
    · have := hinv.named x i hx; simp; omega
  · intro i hi
    by_cases hold : i < rows.length
    · obtain ⟨d1, hd1, hs1, hne1⟩ := hinv.reach i hold
      have hri : (rows ++ [a])[i] = rows[i] := List.getElem_append_left hold
      refine ⟨d1, hd1, ?_, fun d' h' => ?_⟩
      · rw [hri, get_set]
        split
        · rename_i e; rw [← e] at hs1; rw [hd0] at hs1; cases hs1
        · exact hs1
      · rw [hri, get_set]
        split
        · simp
        · exact hne1 d' h'
    · have hi' : i = rows.length := by simp at hi; omega
      subst hi'
      have hra : (rows ++ [a])[rows.length] = a := by simp
      refine ⟨d, hdn, ?_, fun d' h' => ?_⟩
      · rw [hra, get_set, hj]; simp
      · rw [hra, get_set]
        split
        · simp
        · exact hprev d' (Nat.zero_le _) h'
  · refine List.nodup_append.mpr ⟨hinv.rows_nodup, by simp, ?_⟩
    intro x hx y hy e
    simp at hy; subst hy; subst e; exact ha hx
  · intro x x' i hx hx'
    rw [get_set] at hx hx'
    split at hx <;> split at hx'
    · rename_i e1 e2; rw [← e1, ← e2]
    · rename_i e1 _; cases hx; have := hinv.named x' rows.length hx'; omega
    · rename_i _ e2; cases hx'; have := hinv.named x rows.length hx; omega
    · exact hinv.uniq x x' i hx hx'
  · intro i hi dd d' k hdd hs hlt hk
    rw [get_set] at hs hk
    by_cases hold : i < rows.length
    · have hri : (rows ++ [a])[i] = rows[i] := List.getElem_append_left hold
      rw [hri] at hs hk
      split at hs
      · cases hs; omega
      rename_i hjs
      split at hk
      · rename_i hjk
        obtain ⟨d1, hd1, hs1, hne1⟩ := hinv.reach i hold
        have := hinv.uniq _ _ i hs hs1
        have e := at_inj hdd hd1 this
        subst e
        exact absurd (hjk ▸ hd0) (hne1 d' hlt)
      · exact hinv.ord i hold dd d' k hdd hs hlt hk
    · have hi' : i = rows.length := by simp at hi; omega
      subst hi'
      have hra : (rows ++ [a])[rows.length] = a := by simp
      rw [hra] at hs hk
      split at hk
      · rename_i hjk
        split at hs
        · rename_i hjs
          have := at_inj (by omega : d' < n) hdd (hjk.symm.trans hjs); omega
        · exact absurd (hinv.named _ _ hs) (by omega)
      · exact hinv.named _ k hk

/-- **Undo the newest row**: its slot cleared, the table of the rows before it. -/
theorem pop_inv (home : α → Nat) (rows : List α) (a : α) (slots : List Nat) (n : Nat)
    (hinv : Inv (α := α) home (rows ++ [a]) slots n) (j : Nat) (hj : slots[j]? = some (rows.length + 1)) :
    Inv (α := α) home rows (slots.set j 0) n := by
  have hjlt : j < slots.length := (List.getElem?_eq_some_iff.mp hj).1
  have get_set : ∀ x, (slots.set j 0)[x]? = if j = x then some 0 else slots[x]? := by
    intro x; rw [List.getElem?_set]; by_cases e : j = x
    · subst e; simp [hjlt]
    · simp [e]
  have hlen : (rows ++ [a]).length = rows.length + 1 := by simp
  refine ⟨by simp [hinv.len], hinv.pos, hinv.home_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro x i hx
    rw [get_set] at hx
    split at hx
    · cases hx
    · have h1 := hinv.named x i hx
      rw [hlen] at h1
      rcases Nat.lt_or_ge i rows.length with h | h
      · exact h
      · have : i = rows.length := by omega
        subst this
        rename_i hne; exact absurd (hinv.uniq _ _ _ hj hx) hne
  · intro i hi
    have hi' : i < (rows ++ [a]).length := by simp; omega
    obtain ⟨d1, hd1, hs1, hne1⟩ := hinv.reach i hi'
    have hri : (rows ++ [a])[i] = rows[i] := List.getElem_append_left hi
    rw [hri] at hs1 hne1
    refine ⟨d1, hd1, ?_, fun d' h' => ?_⟩
    · rw [get_set]; split
      · rename_i e; rw [← e] at hs1; rw [hj] at hs1; simp at hs1; omega
      · exact hs1
    · rw [get_set]; split
      · rename_i e
        exfalso
        have hk := hinv.ord i hi' d1 d' rows.length hd1 (by rw [hri]; exact hs1) h' (by rw [hri, ← e]; exact hj)
        omega
      · exact hne1 d' h'
  · exact (List.nodup_append.mp hinv.rows_nodup).1
  · intro x x' i hx hx'
    rw [get_set] at hx hx'
    split at hx
    · cases hx
    split at hx'
    · cases hx'
    exact hinv.uniq x x' i hx hx'
  · intro i hi dd d' k hdd hs hlt hk
    have hi' : i < (rows ++ [a]).length := by simp; omega
    have hri : (rows ++ [a])[i] = rows[i] := List.getElem_append_left hi
    rw [get_set] at hs hk
    split at hs
    · cases hs
    split at hk
    · cases hk
    exact hinv.ord i hi' dd d' k hdd (by rw [hri]; exact hs) hlt (by rw [hri]; exact hk)

/-- Where the probe stops: at the row equal to the key, at an empty slot, or out of fuel. -/
inductive PR where
  | hit (i : Nat)
  | empty (j : Nat)
  | full
  deriving DecidableEq

def probeR (rows : List α) (slots : List Nat) (n : Nat) (a : α) : Nat → Nat → PR
  | 0, _ => .full
  | fuel + 1, j =>
    match slots[j]? with
    | none => .full
    | some 0 => .empty j
    | some (i + 1) => if rows[i]? = some a then .hit i else probeR rows slots n a fuel ((j + 1) % n)

def PR.toOpt : PR → Option Nat
  | .hit i => some i
  | _ => none

theorem probeR_toOpt (rows : List α) (slots : List Nat) (n : Nat) (a : α) :
    ∀ fuel j, (probeR rows slots n a fuel j).toOpt = probe rows slots n a fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    simp only [probeR, probe]
    split
    · rfl
    · rfl
    · split
      · rfl
      · exact probeR_toOpt rows slots n a fuel _

/-- An `empty` stop from offset `k` is at the first empty offset (`firstEmpty`) along the path. -/
theorem probeR_empty (rows : List α) (slots : List Nat) (n h : Nat) (a : α) (hpos : 0 < n) :
    ∀ fuel k j, probeR rows slots n a fuel (at_ n h k) = .empty j →
      ∃ d, firstEmpty slots n h fuel k = some d ∧ j = at_ n h d
  | 0, _, _, e => by simp [probeR] at e
  | fuel + 1, k, j, e => by
    simp only [probeR] at e
    split at e
    · cases e
    · rename_i h0; cases e
      exact ⟨k, by simp [firstEmpty, h0], rfl⟩
    · rename_i i hs
      split at e
      · cases e
      · have hk : (at_ n h k + 1) % n = at_ n h (k + 1) := by
          simp only [at_]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hk] at e
        obtain ⟨d, hd, rfl⟩ := probeR_empty rows slots n h a hpos fuel (k + 1) j e
        refine ⟨d, ?_, rfl⟩
        simp [firstEmpty, hs, hd]

end ConPanqueque.ConsModel
