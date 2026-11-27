import ConPanqueque.T.Ind.PiSortTele
import ConRon.Bridge.Frontend.Lines
import ConPanqueque.T.NView

/-!
# `indPiTeleLen`

The syntactic `∀`-telescope length of a declared type (con-leche's `indPiTeleLen`).

`ipt(k, h)`: fuel `k`, expression `h`; returns the count.  Out of fuel it halts (the twin fails).

Also: both telescope walks (`indPiTeleLen`, `piSortTeleLen?`) are read-only, their answers do not depend on
the fuel once it covers the store, they denote con-leche's functions, and they can be called from an `Inv`
world as ghosts (the twin computation after the call is arbitrary).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena
open ConRon.Arena.Frontend (indPiTeleLen)

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

def fIndTele := ofString "indPiTeleLen"

def iptBody (fn : MlS) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.ite (.cmp .equal (vv lDg) (.const 6))
        (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
          (.seq (.call (some (some (.local, lY), none)) fn [.op .sub [vv pFu, .const 1], vv lA2])
            (.return (.op .add [vv lY, .const 1]))))
        (.return (.const 0)))))))

/-! ## Read-only walks -/

theorem ipt_ro : ∀ (k : Nat) (h : EIdx) (s : AState) (n : Nat) (s' : AState),
    indPiTeleLen k h s = .ok (n, s') → s' = s := by
  intro k
  induction k with
  | zero =>
    intro h s n s' hrun
    rw [indPiTeleLen] at hrun
    exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ k ih =>
    intro h s n s' hrun
    rw [indPiTeleLen] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    obtain ⟨hs1, -⟩ := ConRon.Bridge.view_run hv
    subst hs1
    cases v
    case forallE ty b =>
      obtain ⟨m, s₂, hgo, hrest2⟩ := ConRon.Bridge.AM.bind_ok hrest
      have := ih b _ _ _ hgo; subst this
      exact (ConRon.Bridge.AM.pure_ok hrest2).2
    all_goals exact (ConRon.Bridge.AM.pure_ok hrest).2

theorem pst_ro : ∀ (k : Nat) (h : EIdx) (s : AState) (o : Option Nat) (s' : AState),
    piSortTeleLen? k h s = .ok (o, s') → s' = s := by
  intro k
  induction k with
  | zero =>
    intro h s o s' hrun
    rw [piSortTeleLen?] at hrun
    exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ k ih =>
    intro h s o s' hrun
    rw [piSortTeleLen?] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    obtain ⟨hs1, -⟩ := ConRon.Bridge.view_run hv
    subst hs1
    cases v
    case forallE ty b =>
      obtain ⟨m, s₂, hgo, hrest2⟩ := ConRon.Bridge.AM.bind_ok hrest
      have := ih b _ _ _ hgo; subst this
      exact (ConRon.Bridge.AM.pure_ok hrest2).2
    all_goals exact (ConRon.Bridge.AM.pure_ok hrest).2

/-! ## Fuel transfer -/

theorem ipt_fuelAux {s : AState} {rk : EIdx → Nat} (hw : EWFAt s.store rk) :
    ∀ (K k : Nat) (h : EIdx) (n : Nat), indPiTeleLen k h s = .ok (n, s) → (rk h < K ∨ k ≤ K) →
      indPiTeleLen K h s = .ok (n, s) := by
  intro K
  induction K with
  | zero =>
    intro k h n hrun hK
    rcases hK with hK | hK
    · omega
    · have : k = 0 := by omega
      subst this; rw [indPiTeleLen] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ K ih =>
    intro k h n hrun hK
    cases k with
    | zero => rw [indPiTeleLen] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
    | succ k =>
      rw [indPiTeleLen] at hrun ⊢
      obtain ⟨v, s₁, hv, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
      obtain ⟨hs1, hview⟩ := ConRon.Bridge.view_run hv
      subst hs1
      rw [ConRon.Bridge.AM.bind_apply, hv]
      cases v
      case forallE ty b =>
        obtain ⟨m, s₂, hgo, hrest2⟩ := ConRon.Bridge.AM.bind_ok hrest
        have := ipt_ro _ _ _ _ _ hgo; subst this
        have hrb := (hw.childOK h _ hview b (by simp [ENodeView.echildren])).2.1
        have := ih k b m hgo (by omega)
        show (indPiTeleLen K b >>= fun r => pure (r + 1)) s₂ = _
        rw [ConRon.Bridge.AM.bind_apply, this]
        exact hrest2
      all_goals exact hrest

theorem pst_fuelAux {s : AState} {rk : EIdx → Nat} (hw : EWFAt s.store rk) :
    ∀ (K k : Nat) (h : EIdx) (o : Option Nat), piSortTeleLen? k h s = .ok (o, s) → (rk h < K ∨ k ≤ K) →
      piSortTeleLen? K h s = .ok (o, s) := by
  intro K
  induction K with
  | zero =>
    intro k h n hrun hK
    rcases hK with hK | hK
    · omega
    · have : k = 0 := by omega
      subst this; rw [piSortTeleLen?] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ K ih =>
    intro k h n hrun hK
    cases k with
    | zero => rw [piSortTeleLen?] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
    | succ k =>
      rw [piSortTeleLen?] at hrun ⊢
      obtain ⟨v, s₁, hv, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
      obtain ⟨hs1, hview⟩ := ConRon.Bridge.view_run hv
      subst hs1
      rw [ConRon.Bridge.AM.bind_apply, hv]
      cases v
      case forallE ty b =>
        obtain ⟨m, s₂, hgo, hrest2⟩ := ConRon.Bridge.AM.bind_ok hrest
        have := pst_ro _ _ _ _ _ hgo; subst this
        have hrb := (hw.childOK h _ hview b (by simp [ENodeView.echildren])).2.1
        have := ih k b m hgo (by omega)
        show (piSortTeleLen? K b >>= fun r => pure (r.map (· + 1))) s₂ = _
        rw [ConRon.Bridge.AM.bind_apply, this]
        exact hrest2
      all_goals exact hrest

theorem ipt_view {k : Nat} {h : EIdx} {s s' : AState} {n : Nat} (hrun : indPiTeleLen k h s = .ok (n, s')) :
    (s.store.view h).isSome = true := by
  cases k with
  | zero => rw [indPiTeleLen] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ k =>
    rw [indPiTeleLen] at hrun
    obtain ⟨v, s₁, hv, -⟩ := ConRon.Bridge.AM.bind_ok hrun
    rw [(ConRon.Bridge.view_run hv).2]; rfl

theorem pst_view {k : Nat} {h : EIdx} {s s' : AState} {o : Option Nat} (hrun : piSortTeleLen? k h s = .ok (o, s')) :
    (s.store.view h).isSome = true := by
  cases k with
  | zero => rw [piSortTeleLen?] at hrun; exact absurd (ConRon.Bridge.AM.fail_ok hrun) (by simp)
  | succ k =>
    rw [piSortTeleLen?] at hrun
    obtain ⟨v, s₁, hv, -⟩ := ConRon.Bridge.AM.bind_ok hrun
    rw [(ConRon.Bridge.view_run hv).2]; rfl

theorem rank_lt_e' {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) {i : EIdx} (hv : (st.view i).isSome = true) :
    rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · exact Nat.lt_of_lt_of_le (h.rankP i hp hv) (EStore.persCount_le st)
  · exact h.rankS i (by simpa using hp) hv

theorem ipt_fuel {s : AState} (hwf : StoreWF s.store) {k : Nat} {h : EIdx} {n : Nat}
    (hrun : indPiTeleLen k h s = .ok (n, s)) : indPiTeleLen (s.store.nodeCount + 1) h s = .ok (n, s) := by
  obtain ⟨rk, hw⟩ := hwf
  have := rank_lt_e' hw (ipt_view hrun)
  exact ipt_fuelAux hw _ k h n hrun (Or.inl (by omega))

theorem pst_fuel {s : AState} (hwf : StoreWF s.store) {k : Nat} {h : EIdx} {o : Option Nat}
    (hrun : piSortTeleLen? k h s = .ok (o, s)) : piSortTeleLen? (s.store.nodeCount + 1) h s = .ok (o, s) := by
  obtain ⟨rk, hw⟩ := hwf
  have := rank_lt_e' hw (pst_view hrun)
  exact pst_fuelAux hw _ k h o hrun (Or.inl (by omega))

/-! ## Denotation -/

theorem ipt_denote {s s' : AState} (hwf : StoreWF s.store) {h : EIdx} {e : ConLeche.Expr}
    (hd : denoteE s.store h = some e) {k n : Nat} (hrun : indPiTeleLen k h s = .ok (n, s')) :
    n = ConLeche.Frontend.indPiTeleLen e :=
  (ConRon.Bridge.Frontend.indPiTeleLen_run ⟨hwf⟩ k hd hrun).2

theorem pst_denote {s s' : AState} (hwf : StoreWF s.store) {h : EIdx} {e : ConLeche.Expr}
    (hd : denoteE s.store h = some e) {k : Nat} {o : Option Nat} (hrun : piSortTeleLen? k h s = .ok (o, s')) :
    o = e.piSortTeleLen? :=
  (ConRon.Bridge.Frontend.piSortTeleLen?_run ⟨hwf⟩ k hd hrun).2

section
variable {σ : Type}

/-! ## Generic rules -/

/-- A read-only twin computation in front of the twin side is a ghost: drop it. -/
theorem specR_ghost {α β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {x : AM α}
    {k : α → AM β} {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hro : ∀ a s1, x s = .ok (a, s1) → s1 = s) (h : SpecR P c s (x >>= k) R)
    (hk : ∀ a, x s = .ok (a, s) → k a s = m s) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, b, s', hm, hR⟩
  · exact Or.inl hs
  · obtain ⟨a, s1, hx, hka⟩ := ConRon.Bridge.AM.bind_ok hm
    have := hro a s1 hx; subst this
    exact Or.inr ⟨w, hr, b, s', by rw [← hk a hx]; exact hka, hR⟩

/-- The post may remember the twin run. -/
theorem specR_withRun {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s m R) :
    SpecR P c s m (fun a w s' st => m s = .ok (a, s') ∧ R a w s' st) := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a, s', hm, hR⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm, hm, hR⟩

/-! ## The walk -/

/-- The post at fuel `K`: the word is the count, and the count is below the fuel. -/
def PostIPT (C : Ctx) (K : Nat) (n : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ w = BitVec.ofNat 64 n ∧ n < K

theorem postIPT_locals (C : Ctx) (K : Nat) : ∀ (a : Nat) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostIPT C K a w s' st → PostIPT C K a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem ipt_spec (C : Ctx) (hcode : C.code.lookup fIndTele = some ([(pFu, .one), (pH, .one)], iptBody fIndTele, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx),
      SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) (iptBody fIndTele) s
        (indPiTeleLen k h) (PostIPT (ctxH C H) k) := by
  intro k
  induction k with
  | zero =>
    intro _ H s h
    refine specR_prologue (postIPT_locals _ _) (params_noneSP _ _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    exact specR_hangI
  | succ k ih =>
    intro hk H s h
    have ih' := ih (by omega)
    refine specR_prologue (postIPT_locals _ _) (params_noneSP _ _ _) ?_
    rw [indPiTeleLen]
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) hk
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_viewI h (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
      (by decide) (fun vw P htg hsh => ?_)
    have htl : vw.tagN < 2 ^ 64 := by cases vw <;> simp [ENodeView.tagN]
    refine specR_ifI _ (if vw.tagN = 6 then 1 else 0)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        ofNat_eq_c_iff _ 6 htl (by decide)]) (fun hw6 => ?_) (fun hw6 => ?_)
    · -- a `∀`: recurse on the body
      have h6 : vw.tagN = 6 := by by_cases c : vw.tagN = 6; exact c; simp [c] at hw6
      cases vw with
      | forallE ty b =>
        simp only
        refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide)
          (by simp +decide [sev]) rfl (by exact wordsAt_mem1 _ _ _ _ _) ?_
        refine specR_callNIH lY fIndTele [pFu, pH] [.op .sub [vv pFu, .const 1], vv lA2] (iptBody fIndTele)
          [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcode
          ⟨by simp +decide [sev, ctxEnv]; exact ofNat_succ_sub_one k, by simp +decide, trivial⟩
          (PostIPT (ctxH C H) k) (fun n w _ _ => w = BitVec.ofNat 64 n ∧ n < k)
          (fun o w s' st ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨h1, h2⟩, hs⟩)
          (fun u hu _ hlk => fun w hw => by subst hw; exact ih' H s b _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
          (fun n wy s1 H1 hp1 ⟨hwy, hnk⟩ => ?_)
        subst hwy
        exact specR_returnI (.op .add [vv lY, .const 1]) (BitVec.ofNat 64 n + 1)
          (by simp +decide [sev]) (fun t ht' => ⟨H1, hp1, sr_of_eq ht'.sr rfl rfl rfl rfl, by
            apply BitVec.eq_of_toNat_eq; simp, Nat.succ_lt_succ hnk⟩)
      | _ => revert h6; simp [ENodeView.tagN]
    · -- not a `∀`
      have h6 : vw.tagN ≠ 6 := by intro c; simp [c] at hw6
      cases vw with
      | forallE _ _ => revert h6; simp [ENodeView.tagN]
      | _ => exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨H, List.prefix_refl _,
          sr_of_eq ht'.sr rfl rfl rfl rfl, rfl, by omega⟩)

/-! ## Ghost calls from an `Inv` world -/

theorem specR_iptI {α : Type} (C : Ctx)
    (hcode : C.code.lookup fIndTele = some ([(pFu, .one), (pH, .one)], iptBody fIndTele, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64}
    (x y : MlS) (h : EIdx) (K : Nat) (hK : K < 2 ^ 64) (hx : x ∈ D) (hy : Γ.get y = some (Enc.idxW h))
    (hk : ∀ (n : Nat) (H' : List (BitVec 64)), C.H <+: H' → n < K →
      indPiTeleLen (s.store.nodeCount + 1) h s = .ok (n, s) →
      (∀ e, denoteE s.store h = some e → n = ConLeche.Frontend.indPiTeleLen e) →
      SpecR (Inv (ctxH C H') s ((x, BitVec.ofNat 64 n) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fIndTele [.const (BitVec.ofNat 64 K), vv y]) rest)
      s m R := by
  intro t0 ht0
  have hwf : StoreWF s.store := ht0.sr.twf
  revert t0 ht0
  refine specR_ghost (x := indPiTeleLen K h) (k := fun _ => m) (fun a s1 hr => ipt_ro _ _ _ _ _ hr) ?_
    (fun _ _ => rfl)
  refine specR_callNIH x fIndTele [pFu, pH] [.const (BitVec.ofNat 64 K), vv y] (iptBody fIndTele)
    [BitVec.ofNat 64 K, Enc.idxW h] (by decide) rfl hx hcode
    ⟨rfl, by simp only [sev_vv]; exact hy, trivial⟩
    (fun n w s' st => indPiTeleLen K h s = .ok (n, s') ∧ PostIPT (ctxH C C.H) K n w s' st)
    (fun n w s' _ => indPiTeleLen K h s = .ok (n, s') ∧ w = BitVec.ofNat 64 n ∧ n < K)
    (fun n w s' st ⟨hr, H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨hr, h1, h2⟩, hs⟩)
    (fun u hu _ hlk t ht => by
      subst ht; exact specR_withRun (ipt_spec C hcode K hK C.H s h) t (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun n w s' H' hp ⟨hr, hw, hnK⟩ => ?_)
  have := ipt_ro _ _ _ _ _ hr; subst this; subst hw
  exact hk n H' hp hnK (ipt_fuel hwf hr) (fun e hd => ipt_denote hwf hd hr)

theorem specR_pstI {α : Type} (C : Ctx)
    (hcode : C.code.lookup fPiSortTele = some ([(pFu, .one), (pH, .one)], pstBody fPiSortTele, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64}
    (x y : MlS) (h : EIdx) (K : Nat) (hK : K < 2 ^ 64) (hx : x ∈ D) (hy : Γ.get y = some (Enc.idxW h))
    (hk : ∀ (o : Option Nat) (H' : List (BitVec 64)), C.H <+: H' → (∀ n, o = some n → n < K) →
      piSortTeleLen? (s.store.nodeCount + 1) h s = .ok (o, s) →
      (∀ e, denoteE s.store h = some e → o = e.piSortTeleLen?) →
      SpecR (Inv (ctxH C H') s ((x, optW o) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fPiSortTele [.const (BitVec.ofNat 64 K), vv y]) rest)
      s m R := by
  intro t0 ht0
  have hwf : StoreWF s.store := ht0.sr.twf
  revert t0 ht0
  refine specR_ghost (x := piSortTeleLen? K h) (k := fun _ => m) (fun a s1 hr => pst_ro _ _ _ _ _ hr) ?_
    (fun _ _ => rfl)
  refine specR_callNIH x fPiSortTele [pFu, pH] [.const (BitVec.ofNat 64 K), vv y] (pstBody fPiSortTele)
    [BitVec.ofNat 64 K, Enc.idxW h] (by decide) rfl hx hcode
    ⟨rfl, by simp only [sev_vv]; exact hy, trivial⟩
    (fun o w s' st => piSortTeleLen? K h s = .ok (o, s') ∧ PostPST (ctxH C C.H) K o w s' st)
    (fun o w s' _ => piSortTeleLen? K h s = .ok (o, s') ∧ w = optW o ∧ ∀ n, o = some n → n < K)
    (fun o w s' st ⟨hr, H', hp, hs, h1, h2⟩ => ⟨H', hp, ⟨hr, h1, h2⟩, hs⟩)
    (fun u hu _ hlk t ht => by
      subst ht; exact specR_withRun (pst_spec C hcode K hK C.H s h) t (pre_of_lookups hu [pFu, pH] _ rfl hlk))
    (fun o w s' H' hp ⟨hr, hw, hoK⟩ => ?_)
  have := pst_ro _ _ _ _ _ hr; subst this; subst hw
  exact hk o H' hp hoK (pst_fuel hwf hr) (fun e hd => pst_denote hwf hd hr)

/-! ## A name-handle view check -/

def fNvChk := ofString "nameViewChk"

/-- `nvc(h)`: view the name handle `h` (halting when it does not decode), return `0`. -/
def nvcBody : ProgHOL 64 :=
  prologue gaaLocals
    (.seq (.assign .local lFl (vv lFln)) (.seq (.assign .local lDh (vv pH)) (.seq nViewP (.return (.const 0)))))

theorem params_none1 (vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ [(pH, vb)]).get x = none := by
  intro x hx
  simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The post: the store is unchanged in meaning and the name handle views. -/
def PostNVC (C : Ctx) (h : NIdx) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (s'.store.ns.view h).isSome = true

theorem nvc_spec (C : Ctx) (s : AState) (h : NIdx) :
    SpecR (Pre (σ := σ) C s [(pH, Enc.idxW h)]) nvcBody s (pure ()) (PostNVC C h) := by
  refine specR_prologue (fun _ _ _ _ _ ⟨H', hp, hs, hv⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, hv⟩)
    (params_none1 _ _) ?_
  refine specR_assignI lFl (vv lFln) C.FLn (by decide) (by simp +decide [ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_nviewPI h (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
    (by decide) (fun v P hv _ _ => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht' => ⟨C.H, List.prefix_refl _,
    sr_of_eq ht'.sr rfl rfl rfl rfl, by rw [hv]; rfl⟩)

theorem specR_nvcI {α : Type} (C : Ctx) (hcode : C.code.lookup fNvChk = some ([(pH, .one)], nvcBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64}
    (x y : MlS) (h : NIdx) (hx : x ∈ D) (hy : Γ.get y = some (Enc.idxW h))
    (hk : ∀ (H' : List (BitVec 64)) (w : BitVec 64), C.H <+: H' → (s.store.ns.view h).isSome = true →
      SpecR (Inv (ctxH C H') s ((x, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fNvChk [vv y]) rest) s m R := by
  refine specR_ghost (x := (pure () : AM Unit)) (k := fun _ => m)
    (fun a s1 hr => (ConRon.Bridge.AM.pure_ok hr).2) ?_ (fun _ _ => rfl)
  refine specR_callNIH x fNvChk [pH] [vv y] nvcBody [Enc.idxW h] (by decide) rfl hx hcode
    ⟨by simp only [sev_vv]; exact hy, trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostNVC C h a w s' st)
    (fun _ _ s' _ => s' = s ∧ (s'.store.ns.view h).isSome = true)
    (fun _ w s' st ⟨hr, H', hp, hs, hv⟩ => ⟨H', hp, ⟨(ConRon.Bridge.AM.pure_ok hr).2, hv⟩, hs⟩)
    (fun u hu _ hlk t ht => by
      subst ht; exact specR_withRun (nvc_spec C s h) t (pre_of_lookups hu [pH] _ rfl hlk))
    (fun _ w s' H' hp ⟨hs', hv⟩ => by subst hs'; exact hk H' w hp hv)

end

end ConPanqueque.T.Ind
