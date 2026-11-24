import ConPanqueque.T.Comp.Entries
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `ensureSort`

Head-normalize a type and read its sort's level, failing (halting) when the type is not a sort.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def fEns := ofString "ensureSort"
def ensH := ofString "ens_h"
def ensU := ofString "ens_u"

def ensLocals : List MlS := [ensH, ensU, lFl, lDh, lDt, lDg, lDi, lRp, lRn]

def ensBody : ProgHOL 64 := prologue ensLocals
  (.seq (.call (some (some (.local, ensH), none)) fW [vv kFu, vv kD, vv kE])
  (.ite (tagIsE ensH 2)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ensH)) (.seq eViewP
      (.seq (.assign .local ensU (.load .one (vv lRp))) (.return (vv ensU))))))
    hang))

/-- A level handle, the heap extended. -/
def PostLH (C : Ctx) (u : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW u ∧ SR (ctxH C H') s' st ∧ ∃ h, s'.store.view h = some (.sort u)

theorem postLH_locals (C : Ctx) : ∀ (a : LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLH C a w s' st → PostLH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr, hv⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl, hv⟩

section
variable {σ : Type}

theorem ens_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ensLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C ensLocals kParams vals (by decide) (by decide)

/-- **`ensureSort`** over the knot: the port's head normalization and sort read refine the twin's. -/
theorem ens_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (s : AState) (e : EIdx)
    (hW : Callee (σ := σ) C kParams [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s
      ((knot mode C n).whnf d e) (PostK C)) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) ensBody s
      (ensureSort (knot mode C n) C.fe d e) (PostLH C) := by
  refine specR_prologue (postLH_locals C) (ens_none C _) ?_
  unfold ensureSort
  refine Big.specR_callKC ensH fW kParams [vv kFu, vv kD, vv kE] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv],
      by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ hW
    (fun hh s1 H1 hp1 _ => ?_)
  refine Knot.specR_tagIteV ensH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ensH) (Enc.idxW hh) (by decide) (by simp; intro h; exact absurd h (by decide)) ?_
    refine specR_viewP (C := ctxH C H1) hh (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    refine specR_congr (view_bind_eq hh vw _ s1 hv) ?_
    have h2 : vw.tagN = 2 := by rw [htn, htg]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
    refine specR_loadI' ensU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    exact specR_returnI _ (Enc.idxW u) (by simp) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, hh, hv⟩)
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_hangI

end

end ConPanqueque.T.Decl
