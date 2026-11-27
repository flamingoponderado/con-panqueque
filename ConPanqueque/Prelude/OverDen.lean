import ConPanqueque.Prelude.Defs
import ConPanqueque.Prelude.Prep

/-! # The override pass's facts, at con-leche's records

`overOK_of_overW`: what the pass checks on handles (`OverW`) is con-leche's `OverOK` on the records
they denote; and the kept stream records denote con-leche's `filter (keep _)` (`denoteDecls_keep`).
The name tests transport by `declares_denote` (`denoteN` is injective in a well-formed store). -/

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

theorem denoteDecls_len {st : EStore} : ∀ {l : List IDeclaration} {lP : List Declaration},
    denoteDecls st l = some lP → lP.length = l.length
  | [], lP, h => by simp [denoteDecls] at h; subst h; rfl
  | d :: ds, lP, h => by
    simp only [denoteDecls] at h
    split at h
    · rename_i x xs _ hxs
      simp only [Option.some.injEq] at h; subst h
      simp [denoteDecls_len hxs]
    · cases h

theorem denoteDecls_get {st : EStore} : ∀ {l : List IDeclaration} {lP : List Declaration},
    denoteDecls st l = some lP → ∀ i (hi : i < l.length) (hi' : i < lP.length),
      ConRon.Arena.Frontend.denoteDecl st l[i] = some lP[i]
  | [], _, _, i, hi, _ => absurd hi (by simp)
  | d :: ds, lP, h, i, hi, hi' => by
    simp only [denoteDecls] at h
    split at h
    · rename_i x xs hx hxs
      simp only [Option.some.injEq] at h; subst h
      cases i with
      | zero => exact hx
      | succ i => exact denoteDecls_get hxs i (by simpa using hi) (by simpa using hi')
    · cases h

theorem denoteDecls_mem' {st : EStore} {l : List IDeclaration} {lP : List Declaration}
    (h : denoteDecls st l = some lP) {dP : Declaration} (hd : dP ∈ lP) :
    ∃ i, ∃ hi : i < l.length, ∃ hi' : i < lP.length, lP[i] = dP ∧
      ConRon.Arena.Frontend.denoteDecl st l[i] = some dP := by
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hd
  have hl := denoteDecls_len h
  exact ⟨i, by omega, hi', rfl, denoteDecls_get h i (by omega) hi'⟩

theorem denoteDecls_filter {st : EStore} (f : IDeclaration → Bool) (g : Declaration → Bool)
    : ∀ {l : List IDeclaration} {lP : List Declaration},
      (∀ d ∈ l, ∀ dP, ConRon.Arena.Frontend.denoteDecl st d = some dP → f d = g dP) → denoteDecls st l = some lP →
      denoteDecls st (l.filter f) = some (lP.filter g)
  | [], lP, _, h => by simp [denoteDecls] at h; subst h; rfl
  | d :: ds, lP, hfg, h => by
    simp only [denoteDecls] at h
    split at h
    · rename_i x xs hx hxs
      simp only [Option.some.injEq] at h; subst h
      have ih := denoteDecls_filter f g (fun d' hd' => hfg d' (List.mem_cons_of_mem _ hd')) hxs
      simp only [List.filter_cons, ← hfg d (List.mem_cons_self ..) x hx]
      split
      · simp only [denoteDecls, hx, ih]
      · exact ih
    · cases h

/-- No two entries satisfy `f`: the filter has at most one element. -/
theorem filter_len_le_one {α : Type} (f : α → Bool) : ∀ (l : List α),
    (∀ i j (hi : i < l.length) (hj : j < l.length), i < j → f l[i] = true → f l[j] = true → False) →
    (l.filter f).length ≤ 1
  | [], _ => by simp
  | a :: l, h => by
    by_cases ha : f a = true
    · have hnone : ∀ x ∈ l, f x = false := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        cases e : f l[j]
        · rfl
        · exact (h 0 (j + 1) (by simp) (by simp; omega) (by omega) ha (by simpa using e)).elim
      simp only [List.filter_cons, ha, ite_true, List.length_cons]
      rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [hnone x hx])]; simp
    · simp only [List.filter_cons, Bool.not_eq_true] at ha ⊢
      simp only [ha, Bool.false_eq_true, ite_false]
      exact filter_len_le_one f l (fun i j hi hj hij h1 h2 =>
        h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega) (by simpa using h1) (by simpa using h2))

theorem keyOf_denote {st : EStore} {p : IDeclaration} {pP : Declaration}
    (hp : ConRon.Arena.Frontend.denoteDecl st p = some pP) (hk : p.names.head? = some (keyOf p)) :
    denoteN st.ns (keyOf p) = some (preludeKey pP) := by
  have hn := declNames_denote hp
  cases e : p.names with
  | nil => rw [e] at hk; cases hk
  | cons n ns =>
    rw [e] at hk hn
    simp only [List.head?_cons, Option.some.injEq] at hk
    simp only [ConRon.Arena.Frontend.denoteNList] at hn
    cases hd : denoteN st.ns n with
    | none => rw [hd] at hn; simp at hn
    | some nP =>
      cases hds : ConRon.Arena.Frontend.denoteNList st.ns ns with
      | none => rw [hd, hds] at hn; simp at hn
      | some nsP =>
        rw [hd, hds] at hn
        simp only [Option.some.injEq] at hn
        rw [← hk, hd, preludeKey, ← hn]; rfl

theorem declares_val {st : EStore} (hwf : StoreWF st) {d : IDeclaration} {dP : Declaration} {p : IDeclaration}
    {pP : Declaration} (hd : ConRon.Arena.Frontend.denoteDecl st d = some dP)
    (hp : ConRon.Arena.Frontend.denoteDecl st p = some pP) (hk : p.names.head? = some (keyOf p)) (hv : isVal d = true) :
    declares (preludeKey pP) dP = (valName d == keyOf p) := by
  rw [← declares_denote hwf (keyOf_denote hp hk) hd, ConRon.Arena.Frontend.declares, names_val hv]
  by_cases e : valName d = keyOf p
  · simp [List.contains, List.elem, e]
  · have e' : keyOf p ≠ valName d := fun h => e h.symm
    have h1 : (keyOf p == valName d) = false := beq_eq_false_iff_ne.mpr e'
    have h2 : (valName d == keyOf p) = false := beq_eq_false_iff_ne.mpr e
    simp only [List.contains, List.elem, h1, h2]

/-- **The pass's facts are con-leche's `OverOK`.** -/
theorem overOK_of_overW {st : EStore} (hwf : StoreWF st) {Q P : List IDeclaration} {QP PP : List Declaration}
    (hQ : denoteDecls st Q = some QP) (hP : denoteDecls st P = some PP) (h : OverW Q P) : OverOK PP QP := by
  intro pP hpP
  obtain ⟨j, hj, hj', rfl, hpj⟩ := denoteDecls_mem' hP hpP
  have hkey := h.key _ (List.getElem_mem hj)
  refine ⟨fun dP hdP hdec => ?_, ?_⟩
  · obtain ⟨i, hi, hi', rfl, hdi⟩ := denoteDecls_mem' hQ hdP
    have hv := h.val _ (List.getElem_mem hi)
    rw [declares_val hwf hdi hpj hkey hv] at hdec
    have e := h.eq _ (List.getElem_mem hi) _ (List.getElem_mem hj) (by simpa using hdec)
    rw [e] at hdi
    exact Option.some.inj (hdi.symm.trans hpj)
  · refine filter_len_le_one _ QP (fun a b ha hb hab h1 h2 => ?_)
    have hl := denoteDecls_len hQ
    have hda := denoteDecls_get hQ a (by omega) ha
    have hdb := denoteDecls_get hQ b (by omega) hb
    rw [declares_val hwf hda hpj hkey (h.val _ (List.getElem_mem _))] at h1
    rw [declares_val hwf hdb hpj hkey (h.val _ (List.getElem_mem _))] at h2
    have e1 : valName Q[a] = keyOf P[j] := by simpa using h1
    have e2 : valName Q[b] = keyOf P[j] := by simpa using h2
    exact h.uniq a b (by omega) (by omega) hab (by
      rw [e2]; simp only [List.contains_iff_mem, List.mem_map]; exact ⟨P[j], List.getElem_mem hj, rfl⟩)
      (e1.trans e2.symm)

/-- **The kept stream records denote con-leche's rest.** -/
theorem denoteDecls_keep {st : EStore} (hwf : StoreWF st) {Q P : List IDeclaration} {QP PP : List Declaration}
    (hQ : denoteDecls st Q = some QP) (hP : denoteDecls st P = some PP) (h : OverW Q P) :
    denoteDecls st (Q.filter (keepW (P.map keyOf))) = some (QP.filter (keep PP)) := by
  refine denoteDecls_filter _ _ (fun d hdm dP hd => ?_) hQ
  have hv := h.val d hdm
  simp only [keepW, keep, Bool.not_inj_iff]
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
  constructor
  · intro hm
    obtain ⟨p, hpm, hpk⟩ := List.mem_map.mp hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hpm
    have hl := denoteDecls_len hP
    have hpj := denoteDecls_get hP j hj (by omega)
    refine ⟨PP[j], List.getElem_mem _, ?_⟩
    rw [declares_val hwf hd hpj (h.key _ hpm) hv, hpk]; simp
  · intro ⟨pP, hpP, hdec⟩
    obtain ⟨j, hj, hj', rfl, hpj⟩ := denoteDecls_mem' hP hpP
    rw [declares_val hwf hd hpj (h.key _ (List.getElem_mem hj)) hv] at hdec
    exact List.mem_map.mpr ⟨P[j], List.getElem_mem hj, (by simpa using hdec : valName d = keyOf P[j]).symm⟩

end ConPanqueque.Prelude
