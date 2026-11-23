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
  fun c ci hc => denoteNList_total' _ (h.envd c ci hc).1

theorem sr_tyDen {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) :
    ∀ c ci, C.fe.find? c = some ci → (denoteE s.store ci.toConstantVal.type).isSome = true :=
  fun c ci hc => (h.envd c ci hc).2

end ConPanqueque.T
