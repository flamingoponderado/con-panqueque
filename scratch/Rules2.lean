import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem ite_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : ExpHOL 64) (p q : ProgHOL 64) (w : BitVec 64)
    (hc : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.ite c p q) =
      if w ≠ 0 then evaluateHOLFiniteState s p else evaluateHOLFiniteState s q := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  rw [hc]
  by_cases hw : w = 0 <;> simp [hw]

theorem dec_word' {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (v : BitVec 64)
    (body : ProgHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word v))) :
    ∃ L, evaluateHOLFiniteState s (.dec x .one e body) =
      ((evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body).1,
       { (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body).2 with locals := L }) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [he, shapeOfHOLExact, shapeEqHOL]
