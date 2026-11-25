import ConRon.Arena.Denote
import ConRon.Arena.WF
open ConRon.Arena

/-! # Name handles are canonical

In a well-formed name store, two persistent handles denoting the same name are the same handle
(`denoteN_inj`, by induction on the name through the cons tables' `consP`). -/

namespace ConPanqueque.Pipeline

theorem denoteNAux_inj {st : NStore} {rk : NIdx → Nat} (hw : NWFAt st rk) :
    ∀ (n : ConLeche.Name) (f f' : Nat) (i j : NIdx), i.isPersistent = true → j.isPersistent = true →
      denoteNAux st f i = some n → denoteNAux st f' j = some n → i = j := by
  intro n
  induction n with
  | anonymous =>
    intro f f' i j hi hj h1 h2
    cases f with | zero => simp [denoteNAux] at h1 | succ f =>
    cases f' with | zero => simp [denoteNAux] at h2 | succ f' =>
    simp only [denoteNAux, Option.bind_eq_some_iff] at h1 h2
    obtain ⟨v, hv, h1⟩ := h1; obtain ⟨w, hw', h2⟩ := h2
    cases v <;> simp at h1
    cases w <;> simp at h2
    have a := (hw.consP .anonymous i).mpr ⟨hv, hi⟩
    have b := (hw.consP .anonymous j).mpr ⟨hw', hj⟩
    rw [a] at b; exact Option.some.inj b
  | str q s ih =>
    intro f f' i j hi hj h1 h2
    cases f with | zero => simp [denoteNAux] at h1 | succ f =>
    cases f' with | zero => simp [denoteNAux] at h2 | succ f' =>
    simp only [denoteNAux, Option.bind_eq_some_iff] at h1 h2
    obtain ⟨v, hv, h1⟩ := h1; obtain ⟨w, hw', h2⟩ := h2
    cases v with
    | str p s' =>
      cases w with
      | str p' s'' =>
        simp only [Option.map_eq_some_iff, ConLeche.Name.str.injEq] at h1 h2
        obtain ⟨q1, hq1, rfl, rfl⟩ := h1; obtain ⟨q2, hq2, rfl, rfl⟩ := h2
        have hp := (hw.childOK i _ hv p (by simp [NNodeView.children])).2.2 hi
        have hp' := (hw.childOK j _ hw' p' (by simp [NNodeView.children])).2.2 hj
        obtain rfl := ih f f' p p' hp hp' hq1 hq2
        have a := (hw.consP _ i).mpr ⟨hv, hi⟩
        have b := (hw.consP _ j).mpr ⟨hw', hj⟩
        rw [a] at b; exact Option.some.inj b
      | _ => simp at h2
    | _ => simp at h1
  | num q k ih =>
    intro f f' i j hi hj h1 h2
    cases f with | zero => simp [denoteNAux] at h1 | succ f =>
    cases f' with | zero => simp [denoteNAux] at h2 | succ f' =>
    simp only [denoteNAux, Option.bind_eq_some_iff] at h1 h2
    obtain ⟨v, hv, h1⟩ := h1; obtain ⟨w, hw', h2⟩ := h2
    cases v with
    | num p k' =>
      cases w with
      | num p' k'' =>
        simp only [Option.map_eq_some_iff, ConLeche.Name.num.injEq] at h1 h2
        obtain ⟨q1, hq1, rfl, rfl⟩ := h1; obtain ⟨q2, hq2, rfl, rfl⟩ := h2
        have hp := (hw.childOK i _ hv p (by simp [NNodeView.children])).2.2 hi
        have hp' := (hw.childOK j _ hw' p' (by simp [NNodeView.children])).2.2 hj
        obtain rfl := ih f f' p p' hp hp' hq1 hq2
        have a := (hw.consP _ i).mpr ⟨hv, hi⟩
        have b := (hw.consP _ j).mpr ⟨hw', hj⟩
        rw [a] at b; exact Option.some.inj b
      | _ => simp at h2
    | _ => simp at h1

theorem denoteN_inj {st : NStore} (hwf : NStoreWF st) {i j : NIdx} {n : ConLeche.Name}
    (hi : i.isPersistent = true) (hj : j.isPersistent = true)
    (h1 : denoteN st i = some n) (h2 : denoteN st j = some n) : i = j :=
  let ⟨_, hw⟩ := hwf; denoteNAux_inj hw n _ _ i j hi hj h1 h2

end ConPanqueque.Pipeline
