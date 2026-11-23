import ConRon.Arena.WFProofs
open ConRon.Arena

/-!
# On a well-formed store every decoding handle denotes

Strong induction on the store's rank: a node's children decode at a smaller rank (`childOK`), and a view's
denotation is assembled from its children's (`denote*_unfold`). The leaf specs' denotation hypotheses then follow
from `StoreWF` (carried by `SR`) and the handles' validity.
-/

namespace ConPanqueque.T

theorem opt2_isSome {α β γ : Type} {f : α → β → γ} {a : Option α} {b : Option β} (ha : a.isSome = true)
    (hb : b.isSome = true) : (opt2 f a b).isSome = true := by
  cases a <;> cases b <;> simp_all [opt2]

theorem opt3_isSome {α β γ δ : Type} {f : α → β → γ → δ} {a : Option α} {b : Option β} {c : Option γ}
    (ha : a.isSome = true) (hb : b.isSome = true) (hc : c.isSome = true) : (opt3 f a b c).isSome = true := by
  cases a <;> cases b <;> cases c <;> simp_all [opt3]

theorem denoteN_total {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    ∀ n (i : NIdx), rk i < n → (st.view i).isSome = true → (denoteN st i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hr; omega
  | succ n ih =>
    intro i hr hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteN_unfold h hv']
    cases v with
    | anonymous => rfl
    | str p s =>
      have hc := h.childOK i _ hv' p (by simp [NNodeView.children])
      simp [denoteNView, ih p (by omega) hc.1]
    | num p k =>
      have hc := h.childOK i _ hv' p (by simp [NNodeView.children])
      simp [denoteNView, ih p (by omega) hc.1]

theorem denoteN_total' {st : NStore} (h : NStoreWF st) {i : NIdx} (hv : (st.view i).isSome = true) :
    (denoteN st i).isSome = true := by
  obtain ⟨rk, h⟩ := h
  exact denoteN_total h (rk i + 1) i (by omega) hv

theorem denoteL_total {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ n (i : LIdx), rk i < n → (st.view i).isSome = true → (denoteL st i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hr; omega
  | succ n ih =>
    intro i hr hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteL_unfold h hv']
    have hl : ∀ c ∈ v.lchildren, (denoteL st c).isSome = true := fun c hc => by
      have := h.childOK i _ hv' c hc; exact ih c (by omega) this.1
    cases v with
    | zero => rfl
    | succ u => simp [denoteLView, hl u (by simp [LNodeView.lchildren])]
    | max u w => exact opt2_isSome (hl u (by simp [LNodeView.lchildren])) (hl w (by simp [LNodeView.lchildren]))
    | imax u w => exact opt2_isSome (hl u (by simp [LNodeView.lchildren])) (hl w (by simp [LNodeView.lchildren]))
    | param m =>
      have hc := h.nchildOK i _ hv' m (by simp [LNodeView.nchildren])
      simp [denoteLView, denoteN_total' h.ns hc.1]

theorem denoteL_total' {st : LStore} (h : LStoreWF st) {i : LIdx} (hv : (st.view i).isSome = true) :
    (denoteL st i).isSome = true := by
  obtain ⟨rk, h⟩ := h
  exact denoteL_total h (rk i + 1) i (by omega) hv

theorem denoteLList_total {st : LStore} (h : LStoreWF st) :
    ∀ (us : List LIdx), (∀ c ∈ us, (st.view c).isSome = true) → (denoteLList st us).isSome = true
  | [], _ => rfl
  | u :: us, hu => opt2_isSome (denoteL_total' h (hu u (by simp)))
      (denoteLList_total h us (fun c hc => hu c (by simp [hc])))

theorem denoteLs_total' {st : LsStore} (h : LsStoreWF st) {i : LsIdx} (hv : (st.view i).isSome = true) :
    (denoteLs st i).isSome = true := by
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
  rw [denoteLs_unfold hv']
  exact denoteLList_total h.ls v (fun c hc => (h.lchildOK i v hv' c hc).1)

theorem denoteE_total {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    ∀ n (i : EIdx), rk i < n → (st.view i).isSome = true → (denoteE st i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hr; omega
  | succ n ih =>
    intro i hr hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    rw [denoteE_unfold h hv']
    have he : ∀ c ∈ v.echildren, (denoteE st c).isSome = true := fun c hc => by
      have := h.childOK i _ hv' c hc; exact ih c (by omega) this.1
    obtain ⟨rkl, hlw⟩ := h.lss.ls
    have hn : ∀ c ∈ v.nchildren, (denoteN st.ns c).isSome = true := fun c hc =>
      denoteN_total' hlw.ns (h.nchildOK i _ hv' c hc).1
    have hl : ∀ c ∈ v.lchildren, (denoteL st.ls c).isSome = true := fun c hc =>
      denoteL_total' h.lss.ls (h.lchildOK i _ hv' c hc).1
    have hs : ∀ c ∈ v.lschildren, (denoteLs st.lss c).isSome = true := fun c hc =>
      denoteLs_total' h.lss (h.lschildOK i _ hv' c hc).1
    cases v with
    | bvar k => rfl
    | fvar k ty => simp [denoteEView, he ty (by simp [ENodeView.echildren])]
    | sort u => simp [denoteEView, hl u (by simp [ENodeView.lchildren])]
    | const m us => exact opt2_isSome (hn m (by simp [ENodeView.nchildren])) (hs us (by simp [ENodeView.lschildren]))
    | app f a => exact opt2_isSome (he f (by simp [ENodeView.echildren])) (he a (by simp [ENodeView.echildren]))
    | lam ty b => exact opt2_isSome (he ty (by simp [ENodeView.echildren])) (he b (by simp [ENodeView.echildren]))
    | forallE ty b => exact opt2_isSome (he ty (by simp [ENodeView.echildren])) (he b (by simp [ENodeView.echildren]))
    | letE ty w b =>
      exact opt3_isSome (he ty (by simp [ENodeView.echildren])) (he w (by simp [ENodeView.echildren])) (he b (by simp [ENodeView.echildren]))
    | lit l => rfl
    | proj m k e => exact opt2_isSome (hn m (by simp [ENodeView.nchildren])) (he e (by simp [ENodeView.echildren]))

theorem denoteE_total' {st : EStore} (h : StoreWF st) {i : EIdx} (hv : (st.view i).isSome = true) :
    (denoteE st i).isSome = true := by
  obtain ⟨rk, h⟩ := h
  exact denoteE_total h (rk i + 1) i (by omega) hv

end ConPanqueque.T
