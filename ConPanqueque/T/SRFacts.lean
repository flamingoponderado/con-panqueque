import ConPanqueque.T.Denote
import ConPanqueque.T.LvlEqList
import ConRon.Arena.Frontend.Readback
open ConRon.Arena

/-!
# Facts the leaf specs assume, read off the state relation

`SR` carries the twin store's well-formedness, the environment's denotations and the caches' correctness;
with denotation totality, the leaf specs' hypotheses at a represented state follow.
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem sr_stateOK {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) : ConRon.Bridge.StateOK s := ⟨h.twf⟩

theorem sr_lwf {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) : LStoreWF s.store.ls := by
  obtain ⟨rk, w⟩ := h.twf; exact w.lss.ls

theorem sr_lswf {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) : LsStoreWF s.store.lss := by
  obtain ⟨rk, w⟩ := h.twf; exact w.lss

theorem sr_sortDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ e u, s.store.view e = some (.sort u) → ∃ l, denoteL s.store.ls u = some l := by
  intro e u hv
  obtain ⟨rk, w⟩ := h.twf
  have hc := w.lchildOK e _ hv u (by simp [ENodeView.lchildren])
  exact Option.isSome_iff_exists.mp (denoteL_total' w.lss.ls hc.1)

theorem sr_lsDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧
      ∃ hl : vs.length = uh.length, ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)) := by
  intro us uh hv
  have hlw := sr_lswf h
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (denoteLs_total' hlw (by rw [hv]; rfl))
  refine ⟨vs, hvs, ?_⟩
  rw [denoteLs_unfold hv] at hvs
  exact LLeq.denoteLList_get _ uh vs hvs

theorem denoteNList_total' {st : NStore} : ∀ (ns : List NIdx), (∀ n ∈ ns, (denoteN st n).isSome = true) →
    ∃ ks, Frontend.denoteNList st ns = some ks
  | [], _ => ⟨[], rfl⟩
  | n :: ns, h => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (h n (by simp))
    obtain ⟨ks, hks⟩ := denoteNList_total' ns (fun m hm => h m (by simp [hm]))
    exact ⟨k :: ks, by simp [Frontend.denoteNList, hk, hks]⟩

theorem sr_lpDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks :=
  fun c ci hc => denoteNList_total' _ (h.envd.1 c ci hc).1

theorem sr_tyDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c ci, C.fe.find? c = some ci → (denoteE s.store ci.toConstantVal.type).isSome = true :=
  fun c ci hc => (h.envd.1 c ci hc).2.1

theorem sr_lpLen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length + 1 < 2 ^ 60 :=
  fun c ci hc => (h.envd.1 c ci hc).2.2.1

theorem sr_lpLen' {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60 :=
  fun c ci hc => by have := sr_lpLen h c ci hc; omega

theorem sr_defnDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c cv v hint, C.fe.find? c = some (.defnInfo cv v hint) → (denoteE s.store v).isSome = true :=
  fun c cv v hint hc => (h.envd.1 c _ hc).2.2.2.1 cv v hint rfl

/-- `unfoldDefinition`'s environment precondition, from the state relation. -/
theorem sr_ufPre {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ hh n us cv value hint, s.store.view hh = some (.const n us) →
      C.fe.find? n = some (.defnInfo cv value hint) → ∃ ks vsL,
        Frontend.denoteNList s.store.ns cv.levelParams = some ks ∧ denoteLs s.store.lss us = some vsL ∧
        (denoteE s.store value).isSome = true ∧ cv.levelParams.length + 1 < 2 ^ 60 := by
  intro hh n us cv value hint hv hf
  obtain ⟨ks, hks⟩ := sr_lpDen h n _ hf
  have hl := sr_lpLen h n _ hf
  simp only [IConstantInfo.toConstantVal] at hks hl
  obtain ⟨rk, w⟩ := h.twf
  have hc := w.lschildOK hh _ hv us (by simp [ENodeView.lschildren])
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (denoteLs_total' (sr_lswf h) hc.1)
  exact ⟨ks, vs, hks, hvs, sr_defnDen h n cv value hint hf, hl⟩

theorem sr_tblLp {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {T : NIdx} {tbl : IProjTable}
    (hT : C.fe.findTable? T = some tbl) : ∃ ks, Frontend.denoteNList s.store.ns tbl.levelParams = some ks :=
  denoteNList_total' _ (h.envd.2.1 T tbl hT).1

theorem sr_tblBodies {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {T : NIdx} {tbl : IProjTable}
    (hT : C.fe.findTable? T = some tbl) : ∀ b ∈ tbl.bodies.toList, (denoteE s.store b).isSome = true :=
  (h.envd.2.1 T tbl hT).2.1

theorem sr_tblLen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {T : NIdx} {tbl : IProjTable}
    (hT : C.fe.findTable? T = some tbl) : tbl.levelParams.length + 1 < 2 ^ 60 :=
  (h.envd.2.1 T tbl hT).2.2

theorem sr_zeroLevel {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    denoteL s.store.ls C.pins.zeroLevel = some .zero := h.envd.2.2.1

theorem sr_capsLen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {c : NIdx} {cv : IConstantVal}
    {caps : IIndCaps} (hc : C.fe.find? c = some (.indInfo cv caps)) : caps.nparams + caps.nIdx < 2 ^ 63 :=
  (h.envd.1 c _ hc).2.2.2.2 cv caps rfl

theorem sr_recDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {c : NIdx} {cv : IConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List IRecRule} (hc : C.fe.find? c = some (.recInfo cv mI rP isK rules))
    {rl : IRecRule} (hrl : rl ∈ rules) :
    (∀ lv, ((∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv) →
      (∀ u ∈ lv, (denoteL s.store.ls u).isSome = true) ∧ lv.length < 2 ^ 60) ∧
    (∀ lv pins, rl.fire = .nested lv pins → ∀ p ∈ pins, (denoteE s.store p).isSome = true) :=
  h.envd.2.2.2 c cv mI rP isK rules hc rl hrl

theorem sr_sortSome {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {e : EIdx} {u : LIdx}
    (hv : s.store.view e = some (.sort u)) : (denoteL s.store.ls u).isSome = true := by
  obtain ⟨l, hl⟩ := sr_sortDen h e u hv; rw [hl]; rfl

theorem sr_zeroSome {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    (denoteL s.store.ls C.pins.zeroLevel).isSome = true := by
  rw [sr_zeroLevel h]; rfl

end ConPanqueque.T
