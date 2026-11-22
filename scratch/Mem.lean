import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem store_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (dst src : ExpHOL 64)
    (a w : BitVec 64)
    (hd : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
      some (.val (.word a)))
    (hs : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) src =
      some (.val (.word w)))
    (hdom : s.memaddrs a) :
    evaluateHOLFiniteState s (.store dst src) =
      (none, { s with memory := fun c => if c = a then .word w else s.memory c }) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [hd, hs, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]

theorem eval_load_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (a : BitVec 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some (.val (.word a)))
    (hdom : s.memaddrs a) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one e) =
      some (.val (s.memory a)) := by
  simp [evalHOLExact, he, memLoadHOLExact, hdom]
