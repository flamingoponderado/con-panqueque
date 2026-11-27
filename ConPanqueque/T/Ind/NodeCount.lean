import ConPanqueque.T.SameLay

/-!
# The expression store is small, so telescopes are short

`sr_nodeCount`: at a related state, the twin's expression store has fewer than `2⁵⁵` nodes (each of its twenty
tables is below its capacity, below `2³⁰`).  `teleLen_le_nodeCount`: a denoted expression's Π-telescope is no
longer than the store's node count (`denoteE`'s fuel).  Together they bound every telescope the fold meets.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.T.Ind

section
variable {σ : Type}

theorem tabAt_size {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] {t : PanSemStateFiniteExact 64 σ} {L : Layout} {k tier : Nat}
    {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ} {mkI : Nat → ι}
    (h : TabAt t L k tier enc dW tb mkI) : tb.size < 2 ^ 30 := by
  obtain ⟨-, hcap, rows, ders, slots, hu, hR⟩ := h
  have hl := hR.vt.le
  have hn := hR.rel.nodes
  have : tb.size = rows.length := by
    show tb.nodes.size = rows.length
    rw [← hn, Array.length_toList]
  omega

theorem erep_count {t : PanSemStateFiniteExact 64 σ} {L : Layout} {FL : BitVec 64} {st : EStore}
    (h : ERep t L FL st) : st.nodeCount < 2 ^ 55 := by
  have a0 := tabAt_size h.p0; have a1 := tabAt_size h.p1; have a2 := tabAt_size h.p2; have a3 := tabAt_size h.p3
  have a4 := tabAt_size h.p4; have a5 := tabAt_size h.p5; have a6 := tabAt_size h.p6; have a7 := tabAt_size h.p7
  have a8 := tabAt_size h.p8; have a9 := tabAt_size h.p9
  have b0 := tabAt_size h.s0; have b1 := tabAt_size h.s1; have b2 := tabAt_size h.s2; have b3 := tabAt_size h.s3
  have b4 := tabAt_size h.s4; have b5 := tabAt_size h.s5; have b6 := tabAt_size h.s6; have b7 := tabAt_size h.s7
  have b8 := tabAt_size h.s8; have b9 := tabAt_size h.s9
  simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count]
  omega

/-- **The twin's expression store at a related state has fewer than `2⁵⁵` nodes.** -/
theorem sr_nodeCount {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) : s.store.nodeCount < 2 ^ 55 :=
  erep_count h.rep.e

end

theorem teleLen_lt_fuel (st : EStore) : ∀ (f : Nat) (i : EIdx) (e : ConLeche.Expr),
    denoteEAux st f i = some e → ConLeche.Frontend.indPiTeleLen e < f := by
  intro f
  induction f with
  | zero => intro i e h; simp [denoteEAux] at h
  | succ f ih =>
    intro i e h
    cases e with
    | forallE x b =>
      simp only [denoteEAux] at h
      cases hv : st.view i with
      | none => simp [hv] at h
      | some v =>
        cases v <;> simp [hv, opt2, opt3] at h
        all_goals (split at h <;> simp at h)
        all_goals (obtain ⟨-, rfl⟩ := h)
        all_goals (rename_i hb; have := ih _ _ hb; simp only [ConLeche.Frontend.indPiTeleLen]; omega)
    | _ => simp [ConLeche.Frontend.indPiTeleLen]

/-- **A denoted expression's telescope is no longer than the store.** -/
theorem teleLen_le_nodeCount {st : EStore} {i : EIdx} {e : ConLeche.Expr} (h : denoteE st i = some e) :
    ConLeche.Frontend.indPiTeleLen e ≤ st.nodeCount := by
  have := teleLen_lt_fuel st _ i e h
  omega

end ConPanqueque.T.Ind
