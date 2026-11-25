import ConPanqueque.Front.FeedFn

/-! # Frontend initialization: zeroing heap cells

`zeroFillP`: `N` consecutive heap cells from `kZb` set to 0 (`kcH … (replicate N 0) N`), so the
tables start unbound. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

def kZ := ofString "kz"
def kZb := ofString "kzb"
def kZn := ofString "kzn"

def zeroFillP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kZ (.const 0))
    (.seq (.while (.cmp .lower (vv kZ) (vv kZn))
      (.seq (.store (.op .add [vv kZb, .shift .lsl (vv kZ) (.const 3)]) (.const 0))
        (.assign .local kZ (.op .add [vv kZ, .const 1])))) rest)

theorem zeroFill_spec {α : Type} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {rest : ProgHOL 64}
    (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : kZ ∈ D)
    (j0 N : Nat) (hN : j0 + N ≤ C.H.length) (h8 : 8 * (j0 + N) < 2 ^ 64)
    (hZb : Γ.get kZb = some (cellA C j0)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 N))
    (hk : ∀ Γ' : Env, (∀ y, y ≠ kZ → Γ'.get y = Γ.get y) →
      SpecR (Inv (ctxH C (kcH C.H j0 (List.replicate N 0) N)) s Γ' [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (zeroFillP rest) s m R := by
  unfold zeroFillP
  refine specR_assignI kZ (.const 0) 0 hD rfl ?_
  refine specR_dropMem ?_
  let P : LoopPt α → Prop := fun p => p.s = s ∧ p.m = m ∧ ∃ z, z ≤ N ∧
    p.C = ctxH C (kcH C.H j0 (List.replicate N 0) z) ∧ p.Γ.get kZ = some (BitVec.ofNat 64 z) ∧
    ∀ y, y ≠ kZ → p.Γ.get y = Γ.get y
  have hp0 : P ⟨ctxH C (kcH C.H j0 (List.replicate N 0) 0), s, (kZ, 0) :: Γ, m⟩ :=
    ⟨rfl, rfl, 0, by omega, rfl, by simp [Env.get_cons], fun y h => by simp only [Env.get_cons, ite_eq_right h]⟩
  have e0 : ctxH C (kcH C.H j0 (List.replicate N 0) 0) = C := ctxH_self C
  rw [← e0]
  refine (specR_whileT (σ := σ) (D := D) P ⟨ctxH C (kcH C.H j0 (List.replicate N 0) 0), s, (kZ, 0) :: Γ, m⟩ hp0 ?_ : _)
  intro p ⟨hps, hpm, z, hz, hpC, hpz, hpo⟩ _
  refine ⟨_, sev_lower _ (vv kZ) (vv kZn) z N (by simpa [sev, vv] using hpz)
    (by simp only [sev, vv]; rw [hpo _ (by decide)]; exact hZn) (by omega) (by omega), fun hw => ?_, fun hw => ?_⟩
  · have hzN : z = N := by
      by_cases h : z < N
      · simp [bw, h] at hw
      · omega
    subst hzN
    rw [hpC, hps, hpm]
    exact hk p.Γ hpo
  · have hzN : z < N := by
      by_cases h : z < N
      · exact h
      · simp [bw, h] at hw
    have hl : (kcH C.H j0 (List.replicate N 0) z).length = C.H.length := kcH_length _ _ _ _
    have hcell : j0 + z < (ctxH C (kcH C.H j0 (List.replicate N 0) z)).H.length := by
      show j0 + z < (kcH C.H j0 (List.replicate N 0) z).length; omega
    rw [hpC, hps]
    refine step_mono (step_seq (step_heapStoreI (C := ctxH C (kcH C.H j0 (List.replicate N 0) z)) (ctxOK_ctxH hok)
      (.op .add [vv kZb, .shift .lsl (vv kZ) (.const 3)]) (.const 0) (j0 + z) hcell 0 ?_ rfl)
      (step_assignI kZ (.op .add [vv kZ, .const 1]) (BitVec.ofNat 64 (z + 1)) hD ?_)) (fun t ht => ht) ?_
    · simp only [sev, vv, hpz, Option.map_some, show (3 : BitVec 64).toNat = 3 from rfl,
        show (3 : Nat) < 64 by decide, ite_true]
      rw [hpo _ (by decide), hZb, shl3 z (by omega)]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [show cellA (ctxH C (kcH C.H j0 (List.replicate N 0) z)) (j0 + z) = cellA C (j0 + z) from rfl, cellA_add]
    · simp only [sev, vv, hpz, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]
    · intro t' ht'
      refine ⟨⟨ctxH C (kcH C.H j0 (List.replicate N 0) (z + 1)), s, (kZ, BitVec.ofNat 64 (z + 1)) :: p.Γ, m⟩,
        ⟨rfl, rfl, z + 1, by omega, rfl, by simp [Env.get_cons], fun y h => by
          simp only [Env.get_cons, ite_eq_right h]; exact hpo y h⟩, by rw [hpm], ?_⟩
      have e : kcH C.H j0 (List.replicate N 0) (z + 1) = (kcH C.H j0 (List.replicate N 0) z).set (j0 + z) 0 := by
        simp only [kcH]; congr 1; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hzN]
      rw [e]; exact ht'

end ConPanqueque.Front
