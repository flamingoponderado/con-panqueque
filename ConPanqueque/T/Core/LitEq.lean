import ConPanqueque.T.Core.DefeqBinders
import ConPanqueque.T.NameEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Literal equality

Two literal handles' rows compared word by word (the lengths, words `1 …` by `NEq.cmpLoop`, then the tag
words): the encoding is injective (`limbs_inj`, `strW_inj`), so the rows are equal exactly when the literals are.
-/

namespace ConPanqueque.T.LE

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM
open ConPanqueque.V.Enc

def leA := ofString "lea"
def leB := ofString "leb"
def fLe := ofString "litEq"

def leCore : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv leA)) (.seq eViewP
  (.seq (.assign .local lA1 (vv lRp)) (.seq (.assign .local lA2 (vv lRn))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv leB)) (.seq eViewP
  (.ite (.cmp .notEqual (vv lA2) (vv lRn)) (.return (.const 0))
  (.seq (.assign .local lW (.const 1)) (.seq (.assign .local lB (.const 1))
  (.seq NEq.cmpLoop
  (.ite (.cmp .equal (vv lW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lX (.load .one (vv lA1))) (.seq (.assign .local lY (.load .one (vv lRp)))
    (.return (.cmp .equal (vv lX) (vv lY)))))))))))))))))

def leBody : ProgHOL 64 := prologue inst1Locals leCore

theorem encLit_inj (l1 l2 : ConLeche.Literal) (h : encEView (.lit l1) = encEView (.lit l2)) : l1 = l2 := by
  rcases l1 with m1 | s1 <;> rcases l2 with m2 | s2 <;> simp [encEView, Enc.encLit] at h
  · rw [limbs_inj h]
  · rw [strW_inj h]

theorem head_tail_eq {w1 w2 : List (BitVec 64)} (h1 : 1 ≤ w1.length) (h2 : 1 ≤ w2.length) (ht : w1.tail = w2.tail)
    (e0 : w1[0]'(by omega) = w2[0]'(by omega)) : w1 = w2 := by
  rcases w1 with _ | ⟨x, xs⟩
  · simp at h1
  rcases w2 with _ | ⟨y, ys⟩
  · simp at h2
  simp at e0 ht; rw [e0, ht]

section
variable {σ : Type}

theorem le_spec (C : Ctx) (s : AState) (a b : EIdx) (l1 l2 : ConLeche.Literal)
    (hv1 : s.store.view a = some (.lit l1)) (hv2 : s.store.view b = some (.lit l2)) :
    SpecR (σ := σ) (Pre C s [(leA, Enc.idxW a), (leB, Enc.idxW b)]) leBody s (pure (l1 == l2) : AM Bool)
      (WC.PostBS C s) := by
  refine specR_prologue (WC.postBS_locals C s) (Knot.params_none C inst1Locals [leA, leB] [Enc.idxW a, Enc.idxW b]
    (by decide) (by decide)) ?_
  unfold leCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv leA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_congr (m' := ConRon.Arena.view a >>= fun _ => (ConRon.Arena.view b >>= fun _ =>
    (pure (l1 == l2) : AM Bool))) (by rw [Big.view_bind_eq a _ _ s hv1, Big.view_bind_eq b _ _ s hv2]) ?_
  refine ILP.specR_viewIv a (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v1 P1 hv1' _ hl1 => ?_)
  rw [hv1] at hv1'; cases hv1'
  try dsimp only
  refine specR_assignI lA1 (vv lRp) P1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lA2 (vv lRn) (BitVec.ofNat 64 (encEView (ENodeView.lit l1)).length) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv leB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine ILP.specR_viewIv b (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v2 P2 hv2' _ hl2 => ?_)
  rw [hv2] at hv2'; cases hv2'
  try dsimp only
  have hret : ∀ {Γ : Env} {M : Mem}, l1 ≠ l2 →
      SpecR (σ := σ) (Inv C s Γ M DI) (.return (.const 0)) s (pure (l1 == l2)) (WC.PostBS C s) :=
    fun {Γ M} hne => specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨rfl, by simp [hne, boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hpos1 : 1 ≤ (encEView (.lit l1)).length := by rcases l1 with m | str <;> simp [encEView, Enc.encLit]
  have hpos2 : 1 ≤ (encEView (.lit l2)).length := by rcases l2 with m | str <;> simp [encEView, Enc.encLit]
  by_cases hl : (encEView (.lit l1)).length = (encEView (.lit l2)).length
  swap
  · have hne : BitVec.ofNat 64 (encEView (.lit l1)).length ≠ BitVec.ofNat 64 (encEView (.lit l2)).length := by
      intro e; have := congrArg BitVec.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hl this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hret (fun e => hl (by rw [e]))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl]) (fun h => absurd rfl h)
    (fun _ => ?_)
  refine specR_assignI lW (.const 1) 1 (by decide) rfl ?_
  refine specR_assignI lB (.const 1) (BitVec.ofNat 64 (0 + 1)) (by decide) rfl ?_
  rw [← NEq.flagW_zero (encEView (.lit l1)) (encEView (.lit l2))]
  refine NEq.cmpLoop_spec (encEView (.lit l1)) (encEView (.lit l2)) P1 P2 hl hpos1 (by omega)
    (fun i hi => List.mem_append_right _ (wordsAt_get P1 (encEView (.lit l1)) i hi []))
    (fun i hi => wordsAt_get P2 (encEView (.lit l2)) i hi _) (by simp +decide [Env.get, ctxEnv]) (by simp +decide [Env.get, ctxEnv]) (by simp +decide [Env.get, ctxEnv, hl]) (by simp +decide [Env.get, ctxEnv])
    (by simp +decide [Env.get, ctxEnv]) ?_
  have hf := NEq.flagW_full (encEView (.lit l1)) (encEView (.lit l2)) hl hpos1
  by_cases ht : (encEView (.lit l1)).tail = (encEView (.lit l2)).tail
  swap
  · have hf0 : NEq.flagW (encEView (.lit l1)) (encEView (.lit l2)) ((encEView (.lit l1)).length - 1) = 0 := by
      by_contra h; exact ht (hf.mp h)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, hf0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hret (fun e => ht (by rw [e]))
  have hf1 : NEq.flagW (encEView (.lit l1)) (encEView (.lit l2)) ((encEView (.lit l1)).length - 1) ≠ 0 := hf.mpr ht
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hf1)
    (fun h => absurd rfl h) (fun _ => ?_)
  have h1 := wordsAt_get P1 (encEView (.lit l1)) 0 (by omega) []
  have h2 := wordsAt_get P2 (encEView (.lit l2)) 0 (by omega) (wordsAt P1 (encEView (.lit l1)) ++ [])
  refine specR_loadI' lX (vv lA1) P1 (P1 + BitVec.ofNat 64 (8 * 0)) (encEView (.lit l1))[0] (by decide) (by simp +decide [Env.get, ctxEnv]) (by simp)
    (List.mem_append_right _ h1) ?_
  refine specR_loadI' lY (vv lRp) P2 (P2 + BitVec.ofNat 64 (8 * 0)) (encEView (.lit l2))[0] (by decide) (by simp +decide [Env.get, ctxEnv]) (by simp) h2 ?_
  have hiff : (encEView (.lit l1))[0] = (encEView (.lit l2))[0] ↔ l1 = l2 := by
    constructor
    · intro e0
      exact encLit_inj l1 l2 (head_tail_eq hpos1 hpos2 ht e0)
    · intro e; subst e; rfl
  refine specR_returnI _ (boolW (l1 == l2)) ?_ (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases e : l1 = l2
  · simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hiff.mpr e, e, boolW]
  · have : (encEView (.lit l1))[0] ≠ (encEView (.lit l2))[0] := fun x => e (hiff.mp x)
    simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, e, boolW]

end

end ConPanqueque.T.LE
