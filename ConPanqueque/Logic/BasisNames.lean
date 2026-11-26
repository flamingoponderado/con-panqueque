import ConPanqueque.Logic.InternRerun
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.StateOK

/-!
# The pinned basis blocks' names are the reserved names' slices

`BasisKind.decls k` (a no-op rerun past the pins' intern, `InternRerun`) answers a block whose constants'
names are a slice of the pin table's reserved list: `Eq` `[0,3)`, `Nat` `[3,7)`, `Empty` `[7,9)`,
`False` `[9,11)`.
-/

namespace ConPanqueque.Logic.BasisNames

open ConRon.Arena ConRon.Bridge

/-- The reserved slice a pinned block's names are. -/
def resSlice (k : ConLeche.BasisKind) (rs : List NIdx) : List NIdx :=
  match k with
  | .eqK => (rs.drop 0).take 3
  | .natK => (rs.drop 3).take 4
  | .emptyK => (rs.drop 7).take 2
  | .falseK => (rs.drop 9).take 2
  | .quotK => []

theorem denoteNL_drop {st : EStore} : ∀ (n : Nat) (xs : List NIdx) (ns : List ConLeche.Name),
    denoteNL st xs ns → denoteNL st (xs.drop n) (ns.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], _ => by simp [denoteNL]
  | n + 1, _ :: xs, _ :: ns, h => by simp only [List.drop_succ_cons]; exact denoteNL_drop n xs ns h.2
  | _ + 1, [], _ :: _, h => by simp [denoteNL] at h
  | _ + 1, _ :: _, [], h => by simp [denoteNL] at h

theorem denoteNL_take {st : EStore} : ∀ (n : Nat) (xs : List NIdx) (ns : List ConLeche.Name),
    denoteNL st xs ns → denoteNL st (xs.take n) (ns.take n)
  | 0, _, _, _ => by simp [denoteNL]
  | _ + 1, [], [], _ => by simp [denoteNL]
  | n + 1, _ :: xs, _ :: ns, h => by simp only [List.take_succ_cons, denoteNL]; exact ⟨h.1, denoteNL_take n xs ns h.2⟩
  | _ + 1, [], _ :: _, h => by simp [denoteNL] at h
  | _ + 1, _ :: _, [], h => by simp [denoteNL] at h

theorem denoteNL_inj {st : EStore} (hwf : StoreWF st) : ∀ (xs ys : List NIdx) (ns : List ConLeche.Name),
    denoteNL st xs ns → denoteNL st ys ns → xs = ys
  | [], [], _, _, _ => rfl
  | x :: xs, y :: ys, n :: ns, hx, hy => by
    have hnw : NStoreWF st.ns := by
      obtain ⟨_, hr⟩ := hwf; obtain ⟨_, hl⟩ := hr.lss.ls; exact hl.ns
    rw [ConRon.Arena.denoteN_inj hnw hx.1 hy.1, denoteNL_inj hwf xs ys ns hx.2 hy.2]
  | [], _ :: _, [], _, hy => by simp [denoteNL] at hy
  | [], _, _ :: _, hx, _ => by simp [denoteNL] at hx
  | _ :: _, [], _, _, hy => by cases ‹List ConLeche.Name› <;> simp [denoteNL] at * 
  | _ :: _, _, [], hx, _ => by simp [denoteNL] at hx

theorem denoteCV_name {st : EStore} {v : IConstantVal} {cv : ConLeche.ConstantVal}
    (h : Frontend.denoteCV st v = some cv) : denoteN st.ns v.name = some cv.name := by
  unfold Frontend.denoteCV at h
  split at h
  · rename_i n lps ty hn hl ht
    simp only [Option.some.injEq] at h; subst h; exact hn
  · cases h

theorem denoteCI_name {st : EStore} {c : IConstantInfo} {x : ConLeche.ConstantInfo}
    (h : Frontend.denoteCI st c = some x) : denoteN st.ns c.name = some x.name := by
  cases c <;> simp only [Frontend.denoteCI] at h
  all_goals first
    | (obtain ⟨cv, hcv, rfl⟩ := Option.map_eq_some_iff.mp h; exact denoteCV_name hcv)
    | (split at h
       · rename_i cv y hcv hy
         simp only [Option.some.injEq] at h; subst h; exact denoteCV_name hcv
       · cases h)

theorem denoteCIList_names {st : EStore} : ∀ (r : List IConstantInfo) (cs : List ConLeche.ConstantInfo),
    Frontend.denoteCIList st r = some cs → denoteNL st (r.map (·.name)) (cs.map (·.name))
  | [], cs, h => by simp [Frontend.denoteCIList] at h; subst h; simp [denoteNL]
  | c :: r, cs, h => by
    simp only [Frontend.denoteCIList] at h
    split at h
    · rename_i x xs hx hxs
      simp only [Option.some.injEq] at h; subst h
      exact ⟨denoteCI_name hx, denoteCIList_names r xs hxs⟩
    · cases h

/-- **A pinned block's names, on a run that moved nothing, are its reserved slice.** -/
theorem basisDecls_names (k : ConLeche.BasisKind) (hk : k ≠ .quotK) {s : AState} {r : List IConstantInfo}
    (hok : StateOK s) (hp : PinsOK s) (hrun : ConRon.Arena.BasisKind.decls k s = .ok (r, s)) :
    r.map (·.name) = resSlice k s.pins.reserved := by
  obtain ⟨-, hden⟩ := BasisKind.decls_run hok hrun
  have h1 := denoteCIList_names r _ hden
  have hres := hp.reserved
  cases k with
  | quotK => exact absurd rfl hk
  | eqK =>
    have h2 := denoteNL_take 3 _ _ (denoteNL_drop 0 _ _ hres)
    have hv : ((reservedBasisNameValues.drop 0).take 3) = (ConLeche.BasisKind.decls .eqK).map (·.name) := by rfl
    rw [hv] at h2
    exact denoteNL_inj hok.wf _ _ _ h1 h2
  | natK =>
    have h2 := denoteNL_take 4 _ _ (denoteNL_drop 3 _ _ hres)
    have hv : ((reservedBasisNameValues.drop 3).take 4) = (ConLeche.BasisKind.decls .natK).map (·.name) := by rfl
    rw [hv] at h2
    exact denoteNL_inj hok.wf _ _ _ h1 h2
  | emptyK =>
    have h2 := denoteNL_take 2 _ _ (denoteNL_drop 7 _ _ hres)
    have hv : ((reservedBasisNameValues.drop 7).take 2) = (ConLeche.BasisKind.decls .emptyK).map (·.name) := by rfl
    rw [hv] at h2
    exact denoteNL_inj hok.wf _ _ _ h1 h2
  | falseK =>
    have h2 := denoteNL_take 2 _ _ (denoteNL_drop 9 _ _ hres)
    have hv : ((reservedBasisNameValues.drop 9).take 2) = (ConLeche.BasisKind.decls .falseK).map (·.name) := by rfl
    rw [hv] at h2
    exact denoteNL_inj hok.wf _ _ _ h1 h2

end ConPanqueque.Logic.BasisNames
