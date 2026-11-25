import ConPanqueque.T.LvlRest
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `leqCore`: the fuel, the `zero` short-cuts, then `rest`; the block's induction on fuel
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub

def callRestP : ProgHOL 64 :=
  .seq (.call (some (some (.local, lV), none)) fRest [.op .sub [vv pFu, .const 1], vv pLa, vv pLb, vv pD])
    (.return (vv lV))

def leqK : ProgHOL 64 := .ite (eqC lX 0) (.ite signNeg (retK 1) callRestP) callRestP

def leqBody : ProgHOL 64 :=
  prologue leqLocals
  (.ite (eqC pFu 0) (retK 0)
  (.seq (.assign .local lQ (vv pLa)) (lvViewP (.seq (.assign .local lA2 (vv lX))
  (.seq (.assign .local lQ (vv pLb)) (lvViewP
  (.ite (eqC lA2 0) (.ite signNeg leqK (retK 2)) leqK)))))))

theorem leqCore_zero (l r : ConLeche.Level) (d : Int) : ConLeche.Level.leqCore 0 l r d = none := by
  unfold ConLeche.Level.leqCore; rfl

theorem leqCore_succ (n : Nat) (l r : ConLeche.Level) (d : Int) :
    ConLeche.Level.leqCore (n + 1) l r d =
      if l = .zero ∧ d ≥ 0 then some true else if r = .zero ∧ d < 0 then some false
      else ConLeche.Level.rest n l r d := by
  conv => lhs; unfold ConLeche.Level.leqCore

theorem fuel_pred (n : Nat) (h : n + 1 < 2 ^ 64) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp; omega

section
variable {σ : Type}

theorem leq_all (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (hcT : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one))
    (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one)) :
    ∀ n, n < 2 ^ 64 → RecLeq (σ := σ) C leqBody n := by
  intro n
  induction n with
  | zero =>
    intro _ H l r wl wr d s hl hr hd
    refine specR_prologue (postOB_locals _) (params_noneQ _ _) ?_
    rw [leqCore_zero]
    refine specR_ifEq pFu 0 0 (by decide) (by decide) (by simp +decide [ctxEnv, leqParams]) (fun _ => ?_)
      (fun h => absurd rfl h)
    exact specR_retOB 0 _ rfl
  | succ n ih =>
    intro hn H l r wl wr d s hl hr hd
    have ihn := ih (by omega)
    have hok' := ctxOK_H hok H
    have hdl : -2 ^ 63 ≤ d := by omega
    have hdh : d < 2 ^ 63 := by omega
    refine specR_prologue (postOB_locals _) (params_noneQ _ _) ?_
    rw [leqCore_succ]
    refine specR_ifEq pFu (n + 1) 0 hn (by decide) (by simp +decide [ctxEnv, leqParams]) (fun h => absurd h (by omega))
      (fun _ => ?_)
    refine specR_assignI lQ (vv pLa) wl (by decide) (by simp +decide [ctxEnv, leqParams]) ?_
    refine specR_lvViewI hok' wl l (by simp) hl (by simp +decide [ctxEnv, leqParams] <;> rfl)
      (by simp +decide [ctxEnv, leqParams] <;> rfl) lvScratch_DQ (fun Γ1 M1 Pc hp1 hx1 hy1 _ hk1 => ?_)
    refine specR_assignI lA2 (vv lX) (BitVec.ofNat 64 (ltag l)) (by decide) (by simp [hx1]) ?_
    refine specR_assignI lQ (vv pLb) wr (by decide)
      (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams]) ?_
    refine specR_lvViewI hok' wr r (by simp) hr
      (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams] <;> rfl)
      (by simp +decide; rw [hp1 _ (by decide)]; simp +decide [ctxEnv, leqParams] <;> rfl) lvScratch_DQ
      (fun Γ2 M2 Pr hp2 hx2 hy2 hmm2 hk2 => ?_)
    have base : ∀ z, z ∉ lvScratch → z ≠ lQ → z ≠ lA2 →
        Env.get Γ2 z = Env.get (ctxEnv (ctxH C H) ++ leqParams.zip [BitVec.ofNat 64 (n + 1), wl, wr, iW d]) z := by
      intro z h1 h2 h3
      rw [hp2 z h1]; simp only [Env.get_cons, h2, h3, ite_false]; rw [hp1 z h1]; simp [h2]
    have gFu : Env.get Γ2 pFu = some (BitVec.ofNat 64 (n + 1)) := by
      rw [base _ (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
    have gLa : Env.get Γ2 pLa = some wl := by
      rw [base _ (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
    have gLb : Env.get Γ2 pLb = some wr := by
      rw [base _ (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
    have gD : Env.get Γ2 pD = some (iW d) := by
      rw [base _ (by decide) (by decide) (by decide)]; simp +decide [ctxEnv, leqParams]
    have gA2 : Env.get Γ2 lA2 = some (BitVec.ofNat 64 (ltag l)) := by rw [hp2 _ (by decide)]; simp +decide
    have tl := ltag_lt l
    have tr := ltag_lt r
    have callR : SpecR (Inv (σ := σ) (ctxH C H) s Γ2 M2 DQ) callRestP s (pure (ConLeche.Level.rest n l r d))
        (PostOB (ctxH C H)) :=
      callRetOB (C := ctxH C H) fRest leqParams [.op .sub [vv pFu, .const 1], vv pLa, vv pLb, vv pD] restBody
        [BitVec.ofNat 64 n, wl, wr, iW d] (by decide) rfl (by decide) hcT
        ⟨by simp [sev, gFu]; exact fuel_pred n hn, by simp [gLa], by simp [gLb], by simp [gD], trivial⟩ _
        (rest_spec C hok hcS hcN hcM hcC hcB hcI hcR hcE leqBody hcL n (by omega) ihn H l r wl wr d s hl hr
          (by omega))
    have hK : ¬ (l = .zero ∧ d ≥ 0) → SpecR (Inv (σ := σ) (ctxH C H) s Γ2 M2 DQ) leqK s
        (pure (if l = .zero ∧ d ≥ 0 then some true else if r = .zero ∧ d < 0 then some false
          else ConLeche.Level.rest n l r d)) (PostOB (ctxH C H)) := by
      intro hnz
      rw [ite_eq_right hnz]
      unfold leqK
      refine specR_ifEq lX (ltag r) 0 (by omega) (by decide) hx2 (fun e => ?_) (fun e => ?_)
      · have hr0 : r = .zero := by cases r <;> simp_all [ltag]
        refine specR_ifSign d hdl hdh gD (fun hneg => ?_) (fun hpos => ?_)
        · rw [ite_eq_left ⟨hr0, hneg⟩]; exact specR_retOB 1 _ rfl
        · rw [ite_eq_right (fun h => by omega)]; exact callR
      · have hr0 : r ≠ .zero := by intro h; subst h; simp [ltag] at e
        rw [ite_eq_right (fun h => hr0 h.1)]; exact callR
    refine specR_ifEq lA2 (ltag l) 0 (by omega) (by decide) gA2 (fun e => ?_) (fun e => ?_)
    · have hl0 : l = .zero := by cases l <;> simp_all [ltag]
      refine specR_ifSign d hdl hdh gD (fun hneg => hK (fun h => by omega)) (fun hpos => ?_)
      rw [ite_eq_left ⟨hl0, hpos⟩]; exact specR_retOB 2 _ rfl
    · exact hK (fun h => by rw [h.1] at e; simp [ltag] at e)

end

end ConPanqueque.T.LLeq
