import ConPanqueque.T.Ex.Append
import ConPanqueque.T.Big.Pow
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Appending as a function

`appBody`: the block `xs ++ [x]` from the block `xs`, as a callable function with the post `PostBW` (a fresh block
of the given words, the twin's state unchanged).
-/

namespace ConPanqueque.T.ExPre
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG

def aX := ofString "apx"
def fAppend := ofString "appendWord"
def appLocals : List MlS := [lCn, lW, lSrc, lDst, lCi, lCz]
def appParams : List MlS := [lY, aX]
def appBody (C : Ctx) : ProgHOL 64 := prologue appLocals (appendP C aX)

section
variable {σ : Type}

def PostBW (C : Ctx) (s : AState) (ys : List (BitVec 64)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o, C.H <+: H' ∧ C.H.length ≤ o ∧ w = cellA C o ∧ BlkAt H' o ys ∧ SR (ctxH C H') s' st

theorem postBW_locals (C : Ctx) (s : AState) : ∀ (a : List (BitVec 64)) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostBW C s a w s' st → PostBW C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, h2, h0, h3, h4, h5⟩ => ⟨h1, H', o, h2, h0, h3, h4, sr_of_eq h5 rfl rfl rfl rfl⟩

theorem app_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ appLocals → (ctxEnv C ++ appParams.zip vals).get x = none :=
  Knot.params_none C appLocals appParams vals (by decide) (by decide)

theorem app_spec (C : Ctx) (hok : CtxOK C) (s : AState) (oy : Nat) (xs : List (BitVec 64)) (xv : BitVec 64)
    (hblk : BlkAt C.H oy xs) :
    SpecR (σ := σ) (Pre C s (appParams.zip [cellA C oy, xv])) (appBody C) s (pure (xs ++ [xv]))
      (PostBW C s) := by
  refine specR_prologue (postBW_locals C s) (app_none C _) ?_
  exact append_spec (H := C.H) C hok aX xv oy xs (by decide) (by simp +decide [Env.get, appParams, ctxEnv])
    (by simp +decide [Env.get, appParams, ctxEnv]) hblk (by decide) (by simp +decide [Env.get, appParams, ctxEnv])
    (by decide) (fun H' o t hp h0 hb hsr => ⟨rfl, H', o, hp, h0, rfl, hb, hsr⟩)

/-- Calling `appBody`. -/
theorem specR_callApp {β : Type} {C : Ctx} (hok : CtxOK C)
    (hca : C.code.lookup fAppend = some (appParams.map (fun p => (p, ShapeHOL.one)), appBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (ey ex : ExpHOL 64) (oy : Nat)
    (xs : List (BitVec 64)) (xv : BitVec 64) (hx : x ∈ D) (hblk : BlkAt C.H oy xs)
    (hey : sev Γ ey = some (cellA C oy)) (hex : sev Γ ex = some xv)
    (hk : ∀ (H' : List (BitVec 64)) o, C.H <+: H' → BlkAt H' o (xs ++ [xv]) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fAppend [ey, ex]) rest) s m R := by
  refine specR_congr (m' := (pure (xs ++ [xv]) : AM (List (BitVec 64))) >>= fun _ => m) rfl ?_
  refine specR_callNIH x fAppend appParams [ey, ex] (appBody C) [cellA C oy, xv] (by decide) rfl hx hca
    ⟨hey, hex, trivial⟩
    (fun ys w s' st => (pure (xs ++ [xv]) : AM (List (BitVec 64))) s = .ok (ys, s') ∧ PostBW C s ys w s' st)
    (fun ys w s' H' => ys = xs ++ [xv] ∧ s' = s ∧ ∃ o, w = cellA C o ∧ BlkAt H' o ys)
    (fun ys w s' st ⟨hrun, hs, H', o, hp, _, hw, hb, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨H', hp, ⟨rfl, hs, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu appParams _ rfl hlk)
      (app_spec C hok s oy xs xv hblk)))
    (fun ys w s' H' hp ⟨hys, hs, o, hw, hb⟩ => ?_)
  subst hys hs hw
  exact hk H' o hp hb

/-- `specR_callApp`, the fresh block past the caller's heap image. -/
theorem specR_callAppF {β : Type} {C : Ctx} (hok : CtxOK C)
    (hca : C.code.lookup fAppend = some (appParams.map (fun p => (p, ShapeHOL.one)), appBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (ey ex : ExpHOL 64) (oy : Nat)
    (xs : List (BitVec 64)) (xv : BitVec 64) (hx : x ∈ D) (hblk : BlkAt C.H oy xs)
    (hey : sev Γ ey = some (cellA C oy)) (hex : sev Γ ex = some xv)
    (hk : ∀ (H' : List (BitVec 64)) o, C.H <+: H' → C.H.length ≤ o → BlkAt H' o (xs ++ [xv]) →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fAppend [ey, ex]) rest) s m R := by
  refine specR_congr (m' := (pure (xs ++ [xv]) : AM (List (BitVec 64))) >>= fun _ => m) rfl ?_
  refine specR_callNIH x fAppend appParams [ey, ex] (appBody C) [cellA C oy, xv] (by decide) rfl hx hca
    ⟨hey, hex, trivial⟩
    (fun ys w s' st => (pure (xs ++ [xv]) : AM (List (BitVec 64))) s = .ok (ys, s') ∧ PostBW C s ys w s' st)
    (fun ys w s' H' => ys = xs ++ [xv] ∧ s' = s ∧ ∃ o, C.H.length ≤ o ∧ w = cellA C o ∧ BlkAt H' o ys)
    (fun ys w s' st ⟨hrun, hs, H', o, hp, h0, hw, hb, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨H', hp, ⟨rfl, hs, o, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu appParams _ rfl hlk)
      (app_spec C hok s oy xs xv hblk)))
    (fun ys w s' H' hp ⟨hys, hs, o, h0, hw, hb⟩ => ?_)
  subst hys hs hw
  exact hk H' o hp h0 hb

end

end ConPanqueque.T.ExPre
