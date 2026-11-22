import ConPanqueque.ExprFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Fold

namespace ConPanqueque.ExprFold

/-- `fold_case` under an invariant `J`, with the children handled by a function `fn`
whose body is `Bm` (e.g. a memoized version). -/
theorem fold_caseJ {σ : Type} (fn : MlS) (Bm : ProgHOL 64) (g : Fin 10 → ExpHOL 64) (h : Heap) (p c : BitVec 64)
    (J : PanSemStateFiniteExact 64 σ → Prop) (hJ : ∀ t, J t → InMem t h) (hJd : MemDet J)
    (ks : List Kid) (gc : ExpHOL 64) (W : UInt64)
    (hpick : pick c (cases fn g) (.return (.const 0)) = callKids fn (ks.map fun k => (k.x, k.off)) (.return gc))
    (hnd : (ks.map Kid.x).Nodup) (hnu : nU ∉ ks.map Kid.x) (htg : nTg ∉ ks.map Kid.x)
    (hkids : ∀ k ∈ ks, h (p + k.off) = some (.word k.q) ∧
        ∀ t' : PanSemStateFiniteExact 64 σ, t'.code.lookup fn = some ([(nU, .one)], Bm, .one) → J t' →
          t'.locals.lookup nU = some (.val (.word k.q)) → k.c ≤ t'.clock →
          ∃ st, evaluateHOLFiniteState t' Bm = (some (.returned (.val (.word k.r.toBitVec))), st) ∧ PostJ J t' st k.c)
    (hg : ∀ t' : PanSemStateFiniteExact 64 σ, (∀ k ∈ ks, t'.locals.lookup k.x = some (.val (.word k.r.toBitVec))) →
      @evalHOLExact 64 σ _ t'.toExact (fun x => Classical.propDecidable (t'.memaddrs x)) gc =
        some (.val (.word W.toBitVec)))
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code.lookup fn = some ([(nU, .one)], Bm, .one))
    (hj : J s) (hu : s.locals.lookup nU = some (.val (.word p))) (h0 : h p = some (.word c))
    (hck : kidsCost ks ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (body fn g) = (some (.returned (.val (.word W.toBitVec))), st) ∧
      PostJ J s st (kidsCost ks) := by
  obtain ⟨d0, m0⟩ := hJ s hj _ _ h0
  obtain ⟨L, hdec⟩ := dec_word' s nTg (.load .one vU) c (iteChain (cases fn g) (.return (.const 0))) (by
    rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hu]) d0, m0])
  let s1 := setVarHOLFinite nTg (.val (.word c)) s
  have ltg : s1.locals.lookup nTg = some (.val (.word c)) := by simp [s1]
  have hun : nU ≠ nTg := by decide
  have lu : s1.locals.lookup nU = some (.val (.word p)) := by
    simp only [s1]; rw [lookup_setVar_other _ _ hun]; exact hu
  obtain ⟨st, ev, post⟩ := callKidsJ_spec fn Bm h p J hJ hJd ks [] (.return gc) W 0 s1 hnd hnu (by simp) hkids
    (fun t' _ _ j' _ _ hk _ => by
      refine ⟨emptyLocalsHOLFinite t', ?_, ?_⟩
      · rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only; rw [hg t' hk]
        simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL]
        simp only [show (1 : Nat) ≤ 32 from by decide, ite_true]
      · exact ⟨by simp [emptyLocalsHOLFinite], by simp [emptyLocalsHOLFinite],
          hJd t' _ (by simp [emptyLocalsHOLFinite]) (by simp [emptyLocalsHOLFinite]) (by simp [emptyLocalsHOLFinite]) j',
          by simp [emptyLocalsHOLFinite]⟩)
    (by simpa [s1, setVarHOLFinite] using hc)
    (hJd s _ (by simp [s1, setVarHOLFinite]) (by simp [s1, setVarHOLFinite]) (by simp [s1, setVarHOLFinite]) hj)
    lu (by simp) (by simp [s1, setVarHOLFinite]; omega)
  unfold body
  rw [hdec, show setVarHOLFinite nTg (.val (.word c)) s = s1 from rfl, iteChain_eval s1 c ltg, hpick, ev]
  obtain ⟨a1, a2, a3, a4⟩ := post
  exact ⟨_, rfl, by simp [a1, s1, setVarHOLFinite], by simp [a2, s1, setVarHOLFinite],
    hJd _ _ (by simp) (by simp) (by simp) a3, by simp [s1, setVarHOLFinite] at a4; simpa using a4⟩

end ConPanqueque.ExprFold
