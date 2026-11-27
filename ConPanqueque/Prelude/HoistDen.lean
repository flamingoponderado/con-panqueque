import ConPanqueque.Prelude.OverDen

/-! # The hoist check, on handles and at con-leche's records

`opTable`: each pinned `Nat` operation's pin slot and its `natOpDeps` ground's slots
(`opTable_spec`, by `decide`).  `HoistW pins L`: every definition record named by an operation's pin
has each ground (other than itself) named by an earlier value record.  `hoistOK_of_hoistW`: then
con-leche's `HoistOK` holds of the records `L` denotes. -/

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend

namespace ConPanqueque.Prelude

open ConLeche ConLeche.Frontend

/-- Pin slot of each pinned operation, and its ground's slots. -/
def opTable : List (Nat × List Nat) :=
  [(14, [14]), (15, [15]), (16, [14, 16]), (17, [15, 17]), (18, [15, 17, 18]), (19, [19]), (20, [20]),
   (21, [14, 16, 20, 21]), (22, [14, 16, 20, 22]), (23, [20, 22, 23]), (24, [15, 17, 20, 21, 22, 24]),
   (25, [15, 16, 17, 20, 21, 22, 25]), (26, [15, 17, 20, 21, 22, 26]), (27, [16, 17, 20, 27]),
   (28, [16, 20, 21, 28])]

theorem opTable_bool : (ConLeche.natDivModNames ++ ConLeche.natOpNames).all (fun c => opTable.any (fun og =>
    pinNames[og.1]? == some c && natOpDeps c == og.2.map (fun g => pinNames[g]!))) = true := by
  decide +kernel

theorem opTable_lt : ∀ og ∈ opTable, og.1 < 52 ∧ ∀ g ∈ og.2, g < 52 := by decide

theorem opTable_spec {c : Name} (hc : (ConLeche.natDivModNames.contains c || ConLeche.natOpNames.contains c) = true) :
    ∃ o gs, (o, gs) ∈ opTable ∧ pinNames[o]? = some c ∧ natOpDeps c = gs.map (fun g => pinNames[g]!) := by
  have h := opTable_bool
  rw [List.all_eq_true] at h
  have hm : c ∈ ConLeche.natDivModNames ++ ConLeche.natOpNames := by
    simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
    exact List.mem_append.mpr hc
  have := h c hm
  rw [List.any_eq_true] at this
  obtain ⟨⟨o, gs⟩, hog, hb⟩ := this
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨o, gs, hog, hb.1, hb.2⟩

/-- **The hoist condition on handles.** -/
def HoistW (pinH : Array NIdx) (L : List IDeclaration) : Prop :=
  ∀ i (hi : i < L.length), ∀ o gs, (o, gs) ∈ opTable → (∃ cv v h, L[i] = .defnDecl cv v h ∧ cv.name = pinH[o]!) →
    ∀ g ∈ gs, g = o ∨ ∃ k, ∃ hk : k < i, isVal (L[k]'(by omega)) = true ∧ valName (L[k]'(by omega)) = pinH[g]!

theorem denoteNL_get' {st : EStore} : ∀ {hs : List NIdx} {xs : List ConLeche.Name}, denoteNL st hs xs →
    hs.length = xs.length ∧ ∀ i (hi : i < xs.length) (hi' : i < hs.length), denoteN st.ns hs[i] = some xs[i]
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | h :: hs, x :: xs, ⟨h1, h2⟩ => by
    obtain ⟨hl, hg⟩ := denoteNL_get' h2
    refine ⟨by simp [hl], fun i hi hi' => ?_⟩
    cases i with
    | zero => exact h1
    | succ i => exact hg i (by simpa using hi) (by simpa using hi')
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem pinH_denote {st : EStore} {pinH : Array NIdx} (hp : denoteNL st pinH.toList pinNames) (i : Nat)
    (hi : i < 52) : denoteN st.ns pinH[i]! = some pinNames[i]! := by
  obtain ⟨hl, hg⟩ := denoteNL_get' hp
  have hlen : pinNames.length = 52 := by decide
  have hi' : i < pinH.size := by simp at hl; omega
  have := hg i (by omega) (by simpa using hi')
  rw [getElem!_pos pinH i hi', getElem!_pos pinNames i (by omega)]
  simpa using this

/-- **The handle check is con-leche's `HoistOK`.** -/
theorem hoistOK_of_hoistW {st : EStore} (hwf : StoreWF st) {pinH : Array NIdx}
    (hp : denoteNL st pinH.toList pinNames) {L : List IDeclaration} {LP : List Declaration}
    (hL : denoteDecls st L = some LP) (h : HoistW pinH L) : HoistOK LP.toArray := by
  intro i hi c hc g hg
  have hl := denoteDecls_len hL
  simp only [List.size_toArray] at hi
  simp only [List.getElem_toArray] at hc ⊢
  have hdi := denoteDecls_get hL i (by omega) hi
  -- the operation record
  cases hLi : L[i] with
  | defnDecl cv v hint =>
    rw [hLi] at hdi
    simp only [ConRon.Arena.Frontend.denoteDecl] at hdi
    split at hdi
    · rename_i cvP x hcv hx
      simp only [Option.some.injEq] at hdi
      rw [← hdi] at hc
      simp only [isNatOpRecord] at hc
      split at hc
      · rename_i hop
        simp only [Option.some.injEq] at hc
        subst hc
        obtain ⟨o, gs, hog, hpo, hdeps⟩ := opTable_spec hop
        have ho52 := (opTable_lt _ hog).1
        have hn := (denoteCV_inv hcv).1
        have hpl : pinNames.length = 52 := by decide
        have hpo2 : pinNames[o]! = cvP.name := by
          rw [getElem!_pos pinNames o (by omega)]
          rw [List.getElem?_eq_getElem (by omega)] at hpo
          exact Option.some.inj hpo
        have hpo' : denoteN st.ns pinH[o]! = some cvP.name := by rw [pinH_denote hp o ho52, hpo2]
        have hname : cv.name = pinH[o]! := ConRon.Bridge.denoteN_injS hwf hn hpo'
        rw [hdeps] at hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have hg52 := (opTable_lt _ hog).2 g' hg'
        rcases h i (by omega) o gs hog ⟨cv, v, hint, hLi, hname⟩ g' hg' with rfl | ⟨k, hk, hvk, hnk⟩
        · refine ⟨i, Nat.le_refl _, hi, ?_⟩
          rw [← hdi]
          simp only [Declaration.names, List.mem_singleton]
          exact hpo2
        · refine ⟨k, by omega, by omega, ?_⟩
          have hdk := denoteDecls_get hL k (by omega) (by omega)
          have hnl := declNames_denote hdk
          rw [names_val hvk, hnk] at hnl
          simp only [ConRon.Arena.Frontend.denoteNList, pinH_denote hp g' hg52] at hnl
          simp only [Option.some.injEq] at hnl
          rw [← hnl]; simp
      · cases hc
    · cases hdi
  | axiomDecl cv =>
    rw [hLi] at hdi; simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hdi
    obtain ⟨_, _, hdi⟩ := hdi; rw [← hdi] at hc; simp [isNatOpRecord] at hc
  | thmDecl cv v =>
    rw [hLi] at hdi; simp only [ConRon.Arena.Frontend.denoteDecl] at hdi
    split at hdi
    · simp only [Option.some.injEq] at hdi; rw [← hdi] at hc; simp [isNatOpRecord] at hc
    · cases hdi
  | opaqueDecl cv v =>
    rw [hLi] at hdi; simp only [ConRon.Arena.Frontend.denoteDecl] at hdi
    split at hdi
    · simp only [Option.some.injEq] at hdi; rw [← hdi] at hc; simp [isNatOpRecord] at hc
    · cases hdi
  | indDecl b nP =>
    rw [hLi] at hdi; simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hdi
    obtain ⟨_, _, hdi⟩ := hdi; rw [← hdi] at hc; simp [isNatOpRecord] at hc
  | quotDecl k cv =>
    rw [hLi] at hdi; simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hdi
    obtain ⟨_, _, hdi⟩ := hdi; rw [← hdi] at hc; simp [isNatOpRecord] at hc

end ConPanqueque.Prelude
