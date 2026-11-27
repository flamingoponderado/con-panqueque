import ConLeche.Frontend.NatOpGround
import Std.Data.HashMap.Lemmas

/-! # The ground hoist is the identity when every ground is declared in time

`HoistOK ds`: every pinned `Nat` operation record's `natOpDeps` ground is declared at or before the
operation (by some record up to its position).  Then con-leche's `hoistTargets` is empty
(`hoistTargets_ok`), so `hoistNatOpGround` returns the records unchanged.  The program checks
`HoistOK` at run time and hangs otherwise. -/

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

/-- Every operation's ground is declared at or before it. -/
def HoistOK (ds : Array Declaration) : Prop :=
  ∀ i (hi : i < ds.size) c, isNatOpRecord ds[i] = some c →
    ∀ g ∈ natOpDeps c, ∃ k, k ≤ i ∧ ∃ hk : k < ds.size, g ∈ ds[k].names

/-- con-leche's name index, as a fold. -/
def nameIdx (ds : Array Declaration) : Std.HashMap Name Nat :=
  List.foldl (fun b a => List.foldl (fun b n => if (!b.contains n) = true then b.insert n a else b) b ds[a]!.names)
    ∅ (List.range' 0 ds.size)

theorem forIn_id_yield' {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (F : α → β → β)
    (hf : ∀ a b, f a b = ForInStep.yield (F a b)) :
    forIn l init f = l.foldl (fun b a => F a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf]; exact ih _

/-- The index's invariant after the records below `m`. -/
def IdxInv (ds : Array Declaration) (m : Nat) (s : Std.HashMap Name Nat) : Prop :=
  (∀ g j, s[g]? = some j → j < m ∧ ∀ i', i' < j → g ∉ ds[i']!.names) ∧
  (∀ i', i' < m → ∀ g ∈ ds[i']!.names, s.contains g = true)

theorem idxInv_inner (ds : Array Declaration) (m : Nat) :
    ∀ (L : List Name) (s : Std.HashMap Name Nat),
      (∀ g j, s[g]? = some j → j ≤ m ∧ ∀ i', i' < j → g ∉ ds[i']!.names) →
      (∀ i', i' < m → ∀ g ∈ ds[i']!.names, s.contains g = true) →
      let s' := L.foldl (fun b n => if (!b.contains n) = true then b.insert n m else b) s
      (∀ g j, s'[g]? = some j → j ≤ m ∧ ∀ i', i' < j → g ∉ ds[i']!.names) ∧
      (∀ i', i' < m → ∀ g ∈ ds[i']!.names, s'.contains g = true) ∧
      (∀ g ∈ L, s'.contains g = true) ∧ (∀ g, s.contains g = true → s'.contains g = true)
  | [], s, h1, h2 => ⟨h1, h2, fun g hg => absurd hg (by simp), fun _ h => h⟩
  | n :: L, s, h1, h2 => by
    simp only [List.foldl_cons]
    let s1 := if (!s.contains n) = true then s.insert n m else s
    have hs1 : ∀ g, s.contains g = true → s1.contains g = true := by
      intro g hg; simp only [s1]; split
      · rw [Std.HashMap.contains_insert]; simp [hg]
      · exact hg
    have hn1 : s1.contains n = true := by
      simp only [s1]; split
      · rw [Std.HashMap.contains_insert]; simp
      · rename_i h; simpa using h
    have g1 : ∀ g j, s1[g]? = some j → j ≤ m ∧ ∀ i', i' < j → g ∉ ds[i']!.names := by
      intro g j hg
      simp only [s1] at hg; split at hg
      · rename_i hc
        rw [Std.HashMap.getElem?_insert] at hg
        split at hg
        · rename_i he
          have he' : n = g := by simpa using he
          subst he'
          simp only [Option.some.injEq] at hg; subst hg
          refine ⟨Nat.le_refl _, fun i' hi' hm => ?_⟩
          have := h2 i' hi' n hm
          simp [this] at hc
        · exact h1 g j hg
      · exact h1 g j hg
    obtain ⟨r1, r2, r3, r4⟩ := idxInv_inner ds m L s1 g1 (fun i' hi g hg => hs1 g (h2 i' hi g hg))
    refine ⟨r1, r2, fun g hg => ?_, fun g hg => r4 g (hs1 g hg)⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact r4 _ hn1
    · exact r3 g hg

theorem idxInv_fold (ds : Array Declaration) :
    ∀ (k m : Nat) (s : Std.HashMap Name Nat), IdxInv ds m s →
      IdxInv ds (m + k) (List.foldl (fun b a => List.foldl (fun b n => if (!b.contains n) = true then b.insert n a else b)
        b ds[a]!.names) s (List.range' m k))
  | 0, m, s, h => by simpa using h
  | k + 1, m, s, h => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨r1, r2, r3, -⟩ := idxInv_inner ds m ds[m]!.names s
      (fun g j hg => let ⟨a, b⟩ := h.1 g j hg; ⟨Nat.le_of_lt a, b⟩) h.2
    have hI : IdxInv ds (m + 1) _ := ⟨fun g j hg => let ⟨a, b⟩ := r1 g j hg; ⟨Nat.lt_succ_of_le a, b⟩,
      fun i' hi' g hg => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
        · exact r2 i' hlt g hg
        · exact r3 g hg⟩
    have := idxInv_fold ds k (m + 1) _ hI
    rwa [show m + 1 + k = m + (k + 1) by omega] at this

theorem nameIdx_first (ds : Array Declaration) {g : Name} {j : Nat} (h : (nameIdx ds)[g]? = some j)
    {k : Nat} (hk : k < ds.size) (hg : g ∈ ds[k].names) : j ≤ k := by
  have hI := idxInv_fold ds ds.size 0 ∅ ⟨fun g j h => by simp at h, fun i' h => absurd h (by omega)⟩
  rw [Nat.zero_add] at hI
  obtain ⟨-, hfirst⟩ := hI.1 g j h
  by_cases hjk : j ≤ k
  · exact hjk
  · exact absurd (by rw [getElem!_pos ds k hk]; exact hg) (hfirst k (by omega))

theorem forIn_const_id {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (hf : ∀ a ∈ l, f a b = ForInStep.yield b) : (forIn l b f : Id β) = b := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf a (List.mem_cons_self ..)]
    exact ih (fun a' h => hf a' (List.mem_cons_of_mem _ h))

/-- **The hoist moves nothing** when every ground is declared in time. -/
theorem hoistTargets_ok (used : Declaration → Array Name) (ds : Array Declaration) (h : HoistOK ds) :
    hoistTargets used ds = ∅ := by
  unfold hoistTargets
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run_bind, Id.run_pure]
  rw [show [:ds.size].size = ds.size by simp [Std.Legacy.Range.size]]
  rw [forIn_id_yield' (List.range' 0 ds.size 1) (∅ : Std.HashMap Name Nat) _
    (fun (a : Nat) (b : Std.HashMap Name Nat) => List.foldl (fun (b : Std.HashMap Name Nat) (n : Name) =>
      if (!b.contains n) = true then b.insert n a else b) b ds[a]!.names) (fun a b => by
      rw [forIn_id_yield' _ _ _ (fun (n : Name) (b : Std.HashMap Name Nat) => if (!b.contains n) = true then b.insert n a else b)
        (fun n b => by split <;> rfl)]; rfl)]
  rw [show List.foldl (fun b a => List.foldl (fun b n => if (!b.contains n) = true then b.insert n a else b)
    b ds[a]!.names) ∅ (List.range' 0 ds.size 1) = nameIdx ds from rfl]
  simp only [Id.run]
  refine forIn_const_id _ _ _ (fun i hi => ?_)
  have hi' : i < ds.size := by simpa using hi
  rw [getElem!_pos ds i hi']
  cases hc : isNatOpRecord ds[i] with
  | none => rfl
  | some c =>
    simp only
    rw [forIn_const_id _ _ _ (fun g hg => ?_)]
    · rfl
    obtain ⟨k, hki, hk, hgk⟩ := h i hi' c hc g hg
    cases hj : (nameIdx ds)[g]? with
    | none => rfl
    | some j =>
      have := nameIdx_first ds hj hk hgk
      simp only [show ¬ (j > i) by omega, ite_false]; rfl

end ConPanqueque.Prelude
