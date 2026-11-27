import ConPanqueque.T.Quot.PinGen

/-!
# A standard axiom's pin, interned with its handles kept

The twin's standard- and compiler-trust axiom checks compare stored constants (and the axiom record) with
con-leche's pinned `ConstantVal`s, each interned (`internCV`, or `internCI` read back by `toConstantVal`).
Every such pin has at most one level parameter. `genSCV` interns one literal by literal (its plain
interning, `plainCV`), keeping the name in `qN`, the one level parameter (if any) in `qX`, the type in `qT`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.Start ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern

/-- No level parameter, or one (its handle in `qX`). -/
def genLps1 (C : Ctx) : List ConLeche.Name → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | [a], rest => nameP C ((strComps a).getD []) (.seq (.assign .local qX (vv vPn)) rest)
  | _, _ => hang

/-- A standard pin's constant value, its handles kept in `qN`, `qX`, `qT`. -/
def genSCV (C : Ctx) (cv : ConLeche.ConstantVal) (rest : ProgHOL 64) : ProgHOL 64 :=
  nameP C ((strComps cv.name).getD []) (.seq (.assign .local qN (vv vPn))
    (genLps1 C cv.levelParams (genE C 0 cv.type (.seq (.assign .local qT (vv (ge 0))) rest))))

/-- The level parameters' handle in `qX` (none, or the one). -/
def LpsQ (Γ : Env) : List NIdx → Prop
  | [] => True
  | [h] => Γ.get qX = some (Enc.idxW h)
  | _ => False

/-- A standard pin's handles. -/
def PinS (Γ : Env) (r : IConstantVal) : Prop :=
  Γ.get qN = some (Enc.idxW r.name) ∧ LpsQ Γ r.levelParams ∧ Γ.get qT = some (Enc.idxW r.type)

section
variable {σ : Type}

theorem q_ne_gv (c : Char) (j : Nat) {x : MlS} (hx : x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) :
    x ≠ gv c j := by
  intro e; subst e
  have := gv_ne_q c j
  rcases hx with h | h | h | h | h | h <;> simp_all

/-- **`genSCV`**: the pin's constant value interned (`plainCV`), its handles in `qN`, `qX`, `qT`. -/
theorem genSCV_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} {D : List MlS}
    (G : GenEnv C D 12) (hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ D)
    (cv : ConLeche.ConstantVal) (hcv : CVLit 0 12 cv) (hl : cv.levelParams.length ≤ 1)
    (H0 : List (BitVec 64)) (rest : ProgHOL 64) (Γ : Env) (M : Mem) (s : AState)
    {β : Type} {k : IConstantVal → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ r s' Γ' H', H0 <+: H' → AgreeQ Γ Γ' → plainCV cv s = .ok (r, s') → PinS Γ' r →
      r.levelParams.length = cv.levelParams.length → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k r) R) :
    SpecR (Inv (ctxH C H0) s Γ M D) (genSCV C cv rest) s (plainCV cv >>= k) R := by
  obtain ⟨hn, hls, he, hde⟩ := hcv
  obtain ⟨nm, lps, ty⟩ := cv
  simp only at hn hls he hde hl
  unfold genSCV
  simp only [plainCV, bind_assoc]
  refine name_stepP ra G _ hn H0 _ Γ M s (fun h1 s1 Γ1 hf1 hv1 hr1 => ?_)
  refine specR_assignI qN (vv vPn) (Enc.idxW h1) (hq qN (by simp)) (by simp only [sev_vv, hv1]) ?_
  -- the level parameters: a frame, the handles, the run
  have hlps : ∀ {γ : Type} {kk : List NIdx → AM γ} {RR : γ → BitVec 64 → AState → PState σ → Prop}
      (r2 : ProgHOL 64),
      (∀ hs s2 Γ2, Frontend.internNameList lps s1 = .ok (hs, s2) →
        (∀ y, y ≠ vPn → y ≠ vKa → y ≠ qX → Γ2.get y = Env.get ((qN, Enc.idxW h1) :: Γ1) y) →
        LpsQ Γ2 hs → hs.length = lps.length → SpecR (Inv (ctxH C H0) s2 Γ2 [] D) r2 s2 (kk hs) RR) →
      SpecR (Inv (ctxH C H0) s1 ((qN, Enc.idxW h1) :: Γ1) [] D) (genLps1 C lps r2) s1
        (Frontend.internNameList lps >>= kk) RR := by
    intro γ kk RR r2 hk2
    match lps, hl, hk2 with
    | [], _, hk2 =>
      simp only [genLps1, Frontend.internNameList, pure_bind]
      exact hk2 [] s1 _ rfl (fun _ _ _ _ => rfl) trivial rfl
    | [a], _, hk2 =>
      simp only [genLps1, Frontend.internNameList, bind_assoc, pure_bind]
      refine name_stepP ra G a (hls a (by simp)) H0 _ _ [] s1 (fun h s2 Γ2 hf2 hv2 hr2 => ?_)
      refine specR_assignI qX (vv vPn) (Enc.idxW h) (hq qX (by simp)) (by simp only [sev_vv, hv2]) ?_
      refine hk2 [h] s2 _ (by simp only [Frontend.internNameList, bind_assoc, pure_bind]; exact bind_ok_of hr2 rfl)
        (fun y h1' h2' h3' => ?_) (by simp [LpsQ, Env.get_cons]) rfl
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e h3')]
      exact hf2 y h1' h2'
    | _ :: _ :: _, hl', _ => simp at hl'
  refine hlps _ (fun hs s2 Γ2 hr2 hf2 hL2 hlen2 => ?_)
  refine genE_spec ra C G.hok G.hf G.hA G.hc D G.hPn G.hKa 12 G.hD _ 0 H0 _ Γ2 [] s2 he (by omega)
    (fun h3 s3 Γ3 H3 hp3 ag3 hv3 hr3 => ?_)
  refine specR_assignI qT (vv (ge 0)) (Enc.idxW h3) (hq qT (by simp)) (by simp only [sev_vv, hv3]) ?_
  simp only [pure_bind]
  have k3 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) → Γ3.get x = Γ2.get x := fun x hx =>
    ag3 x (fun c j _ => q_ne_gv c j hx) (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine hk ⟨h1, hs, h3⟩ s3 _ H3 hp3 ?_ (bind_ok_of hr1 (bind_ok_of hr2 (bind_ok_of hr3 rfl))) ⟨?_, ?_, ?_⟩ hlen2
  · refine fun y hy h1' h2' hN _ hT _ hX _ => ?_
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hT), ag3 y (fun c j _ => hy c j) h1' h2',
      hf2 y h1' h2' hX, Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e hN)]
    exact hf1 y h1' h2'
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)), k3 qN (Or.inl rfl)]
    have := hf2 qN (by decide) (by decide) (by decide)
    rw [this]; simp [Env.get_cons]
  · show LpsQ _ hs
    have kx : Env.get ((qT, Enc.idxW h3) :: Γ3) qX = Γ2.get qX := by
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide)),
        k3 qX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
    match hs, hL2 with
    | [], _ => trivial
    | [h], hL2 => show _ = _; rw [kx]; exact hL2
  · simp [Env.get_cons]

end

end ConPanqueque.T.Quot
