import ConPanqueque.Logic.Basic
import ConPanqueque.ConsProbe

/-! # Straight-line stores of constants

`storesP l` stores each word of the list `l` of (address, word) pairs, in order.  Its memory
afterwards is `updL`; with distinct addresses, a listed address holds its word and any other
address keeps its old content. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact ConPanqueque.Logic

namespace ConPanqueque.Start

def storesP : List (BitVec 64 × BitVec 64) → ProgHOL 64
  | [] => .skip
  | (a, w) :: l => .seq (.store (.const a) (.const w)) (storesP l)

def updL (m : BitVec 64 → HolWordLab 64) : List (BitVec 64 × BitVec 64) → (BitVec 64 → HolWordLab 64)
  | [] => m
  | (a, w) :: l => updL (fun c => if c = a then .word w else m c) l

theorem storesP_spec {σ : Type} (l : List (BitVec 64 × BitVec 64)) (t : PanSemStateFiniteExact 64 σ)
    (hdom : ∀ p ∈ l, t.memaddrs p.1) :
    evaluateHOLFiniteState t (storesP l) = (none, { t with memory := updL t.memory l }) := by
  induction l generalizing t with
  | nil => simp only [storesP, updL]; rw [ConPanqueque.ConsProbe.skip_eval]
  | cons p l ih =>
    obtain ⟨a, w⟩ := p
    simp only [storesP, updL]
    rw [seq_normal _ (store_word t (.const a) (.const w) a w (by simp [evalHOLExact]) (by simp [evalHOLExact])
      (hdom _ (List.mem_cons_self ..)))]
    exact ih _ (fun q hq => hdom q (List.mem_cons_of_mem _ hq))

theorem updL_not_mem (m : BitVec 64 → HolWordLab 64) (l : List (BitVec 64 × BitVec 64)) (c : BitVec 64)
    (h : c ∉ l.map Prod.fst) : updL m l c = m c := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [updL]; rw [ih _ h.2, ite_eq_right h.1]

theorem updL_mem (m : BitVec 64 → HolWordLab 64) (l : List (BitVec 64 × BitVec 64)) (c w : BitVec 64)
    (hn : (l.map Prod.fst).Nodup) (h : (c, w) ∈ l) : updL m l c = .word w := by
  induction l generalizing m with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨a, w'⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [updL]
    rcases List.mem_cons.mp h with e | hm
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [updL_not_mem _ _ _ hn.1, ite_eq_left rfl]
    · exact ih _ hn.2 hm

end ConPanqueque.Start
