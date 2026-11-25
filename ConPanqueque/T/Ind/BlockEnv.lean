import ConPanqueque.T.Ind.RecFire
import ConRon.Bridge.Inductives.BlockTail

/-!
# The block's temporary environment, read as the block table

`blockReadsAt` pushes the block's constants temporarily (`consBlockRecsTemp`) and pops them after
`recsRead`.  The port never pushes: the finder reads the block table first and the index after
(`bfLook`).  These are the twin-side facts tying the two together.
-/

namespace ConPanqueque.T.Ind

open ConRon.Arena ConRon.Bridge

/-- The temporary pushes answer with the newest pushed constant at a name, else the index. -/
theorem crt_find : ∀ (cs : List IConstantInfo) (fe : IFEnv) (prevs : List (NIdx × Option IConstantInfo)) (n : NIdx),
    (consBlockRecsTemp cs fe prevs).1.find? n =
      match cs.reverse.find? (fun ci => ci.name == n) with
      | some ci => some ci
      | none => fe.find? n
  | [], fe, prevs, n => by simp [consBlockRecsTemp]
  | ci :: rest, fe, prevs, n => by
    simp only [consBlockRecsTemp]
    rw [crt_find rest (fe.push ci) _ n, IFEnv.find?_push, List.reverse_cons, List.find?_append]
    cases h : rest.reverse.find? (fun ci => ci.name == n) with
    | some c => simp
    | none =>
      by_cases hb : (ci.name == n) = true
      · simp [hb]
      · simp [hb]

/-- The block table answers as the temporary pushes when its entries are the pushed constants at their
own names. -/
theorem bfLook_crt (es : List (NIdx × Nat × IConstantInfo)) (fe : IFEnv)
    (hn : ∀ e ∈ es, e.1 = e.2.2.name) (n : NIdx) :
    bfLook es fe n = (consBlockRecsTemp (es.map (fun e => e.2.2)) fe []).1.find? n := by
  rw [crt_find]
  unfold bfLook
  have key : ∀ (l : List (NIdx × Nat × IConstantInfo)), (∀ e ∈ l, e.1 = e.2.2.name) →
      (l.find? (fun e => e.1 == n)).map (fun e => e.2.2) = (l.map (fun e => e.2.2)).find? (fun ci => ci.name == n) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons e l ih =>
      have he := hl e (List.mem_cons_self ..)
      simp only [List.find?_cons, List.map_cons]
      rw [he]
      by_cases hb : (e.2.2.name == n) = true
      · simp [hb]
      · simp only [hb]; exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  have hk := key es.reverse (fun e he => hn e (List.mem_reverse.mp he))
  rw [List.map_reverse] at hk
  rw [← hk]
  cases es.reverse.find? (fun e => e.1 == n) <;> rfl

/-- The pops give back an index answering as before the pushes, flags set back. -/
theorem crt_pop_find (cs : List IConstantInfo) (fe : IFEnv) (n : NIdx) :
    (((consBlockRecsTemp cs fe []).2.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
      (consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit).find? n = fe.find? n := by
  obtain ⟨news, hn, hf⟩ := ConRon.Bridge.Inductives.BT.consBlockRecsTemp_pop cs fe []
  simp only [List.nil_append] at hn
  rw [hn]
  exact hf.find? n

end ConPanqueque.T.Ind
