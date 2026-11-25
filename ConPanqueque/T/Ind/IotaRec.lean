import ConPanqueque.T.Ind.DropVars

/-!
# What every rule of a recursor reads off its type (`iotaRecMajor`)

An `IotaRec` is a block `[pre, minors, us, params]`: the rule prefix (cells from `pre + 1`, as `stripPis` leaves
them), the minor premises' positions, the major's levels and its parameters (the index variables dropped).
`tsub(a, b)` is the truncated difference.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.ExSP ConPanqueque.T.ExI
open ConPanqueque.T.WC

def tsA := ofString "ts_a"
def tsB := ofString "ts_b"
def fTSub := ofString "tsub"

def tsBody : ProgHOL 64 := prologue []
  (.ite (.cmp .lower (vv tsA) (vv tsB)) (.return (.const 0)) (.return (.op .sub [vv tsA, vv tsB])))

section
variable {σ : Type}

theorem ts_spec (C : Ctx) (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s [(tsA, BitVec.ofNat 64 a), (tsB, BitVec.ofNat 64 b)]) tsBody s
      (pure (a - b)) (PostN (ctxH C H)) := by
  refine specR_prologue (postN_locals _) (fun x hx => by simp at hx) ?_
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower _ (vv tsA) (vv tsB) a b (by simp +decide [sev, Env.get, ctxEnv])
    (by simp +decide [sev, Env.get, ctxEnv]) (by omega) (by omega)) (fun h => ?_) (fun h => ?_)
  · have c : a < b := by by_cases c : a < b; exact c; simp [bw, c] at h
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by rw [Nat.sub_eq_zero_of_le (by omega)]; rfl,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have c : ¬ a < b := by intro c; simp [bw, c] at h
    exact specR_returnI _ (BitVec.ofNat 64 (a - b))
      (by simp +decide [sev, Env.get, ctxEnv]; exact ofNat_sub_small a b (by omega) (by omega))
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- A `tsub` call: the difference, the state and heap kept. -/
theorem rb_tsub (C : Ctx) (hc : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one))
    (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (H : List (BitVec 64)) (s : AState)
    {β : Type} {Γ : Env} {D : List MlS} {M : Mem} {rest : ProgHOL 64} {k : Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (ea eb : ExpHOL 64) (hx : x ∈ D)
    (hea : sev Γ ea = some (BitVec.ofNat 64 a)) (heb : sev Γ eb = some (BitVec.ofNat 64 b))
    (hk : ∀ H1, H <+: H1 → SpecR (Inv (ctxH C H1) s ((x, BitVec.ofNat 64 (a - b)) :: Γ) [] D) rest s (k (a - b)) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, x), none)) fTSub [ea, eb]) rest) s
      (pure (a - b) >>= k) R :=
  specR_callNIH (C := ctxH C H) x fTSub [tsA, tsB] [ea, eb] tsBody [BitVec.ofNat 64 a, BitVec.ofNat 64 b] (by decide) rfl
    hx hc ⟨hea, heb, trivial⟩
    (fun r w s' st => (pure (a - b) : AM Nat) s = .ok (r, s') ∧ PostN (ctxH C H) r w s' st)
    (fun r w s' H' => w = BitVec.ofNat 64 r ∧ r = a - b ∧ s' = s)
    (fun r w s' st ⟨hr, H', hp', hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      exact ⟨H', hp', ⟨hw, hr.1.symm, hr.2.symm⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [tsA, tsB] _ rfl hlk)
      (ts_spec C a b ha hb H s)))
    (fun r w s' H' hp' ⟨hw, hr, hs'⟩ => by subst hw; subst hr; subst hs'; exact hk H' hp')

end

end ConPanqueque.T.Ind
