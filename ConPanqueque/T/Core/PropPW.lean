import ConPanqueque.T.Core.SubstPW
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# PropRead's head readers: `residualPW`

`Option PropWhen` in the port (`optPW`): `none` the word `0`, else the datum (`pwEnc`). `residualPW` of a sort
`u`: `never` when `u` is never zero (`nz`), else the block of its zero-ness parameters (`zc` into an empty block).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def rwH := ofString "prw_rwh"
def rwE := ofString "prw_rwe"
def rwU := ofString "prw_rwu"
def rwZ := ofString "prw_rwz"
def rwA := ofString "prw_rwa"
def rwR := ofString "prw_rwr"
def fRw := ofString "residualPW"

@[simp] theorem prw_rwH_ne_rwE : rwH ≠ rwE := by decide
@[simp] theorem prw_rwH_ne_rwU : rwH ≠ rwU := by decide
@[simp] theorem prw_rwH_ne_rwZ : rwH ≠ rwZ := by decide
@[simp] theorem prw_rwH_ne_rwA : rwH ≠ rwA := by decide
@[simp] theorem prw_rwH_ne_rwR : rwH ≠ rwR := by decide
@[simp] theorem prw_rwH_ne_lFl : rwH ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwH : lFl ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lDh : rwH ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwH : lDh ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lDt : rwH ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwH : lDt ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lDg : rwH ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwH : lDg ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lDi : rwH ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwH : lDi ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lRp : rwH ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwH : lRp ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lRn : rwH ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwH : lRn ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lFle : rwH ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwH : lFle ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lKb : rwH ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwH : lKb ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lDir : rwH ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwH : lDir ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lFln : rwH ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwH : lFln ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lFll : rwH ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwH : lFll ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_lFls : rwH ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwH : lFls ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_kFu : rwH ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwH : kFu ≠ rwH := by decide
@[simp] theorem prw_rwH_ne_kD : rwH ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwH : kD ≠ rwH := by decide
@[simp] theorem prw_rwE_ne_rwH : rwE ≠ rwH := by decide
@[simp] theorem prw_rwE_ne_rwU : rwE ≠ rwU := by decide
@[simp] theorem prw_rwE_ne_rwZ : rwE ≠ rwZ := by decide
@[simp] theorem prw_rwE_ne_rwA : rwE ≠ rwA := by decide
@[simp] theorem prw_rwE_ne_rwR : rwE ≠ rwR := by decide
@[simp] theorem prw_rwE_ne_lFl : rwE ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwE : lFl ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lDh : rwE ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwE : lDh ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lDt : rwE ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwE : lDt ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lDg : rwE ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwE : lDg ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lDi : rwE ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwE : lDi ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lRp : rwE ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwE : lRp ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lRn : rwE ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwE : lRn ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lFle : rwE ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwE : lFle ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lKb : rwE ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwE : lKb ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lDir : rwE ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwE : lDir ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lFln : rwE ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwE : lFln ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lFll : rwE ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwE : lFll ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_lFls : rwE ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwE : lFls ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_kFu : rwE ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwE : kFu ≠ rwE := by decide
@[simp] theorem prw_rwE_ne_kD : rwE ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwE : kD ≠ rwE := by decide
@[simp] theorem prw_rwU_ne_rwH : rwU ≠ rwH := by decide
@[simp] theorem prw_rwU_ne_rwE : rwU ≠ rwE := by decide
@[simp] theorem prw_rwU_ne_rwZ : rwU ≠ rwZ := by decide
@[simp] theorem prw_rwU_ne_rwA : rwU ≠ rwA := by decide
@[simp] theorem prw_rwU_ne_rwR : rwU ≠ rwR := by decide
@[simp] theorem prw_rwU_ne_lFl : rwU ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwU : lFl ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lDh : rwU ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwU : lDh ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lDt : rwU ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwU : lDt ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lDg : rwU ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwU : lDg ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lDi : rwU ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwU : lDi ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lRp : rwU ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwU : lRp ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lRn : rwU ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwU : lRn ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lFle : rwU ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwU : lFle ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lKb : rwU ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwU : lKb ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lDir : rwU ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwU : lDir ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lFln : rwU ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwU : lFln ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lFll : rwU ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwU : lFll ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_lFls : rwU ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwU : lFls ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_kFu : rwU ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwU : kFu ≠ rwU := by decide
@[simp] theorem prw_rwU_ne_kD : rwU ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwU : kD ≠ rwU := by decide
@[simp] theorem prw_rwZ_ne_rwH : rwZ ≠ rwH := by decide
@[simp] theorem prw_rwZ_ne_rwE : rwZ ≠ rwE := by decide
@[simp] theorem prw_rwZ_ne_rwU : rwZ ≠ rwU := by decide
@[simp] theorem prw_rwZ_ne_rwA : rwZ ≠ rwA := by decide
@[simp] theorem prw_rwZ_ne_rwR : rwZ ≠ rwR := by decide
@[simp] theorem prw_rwZ_ne_lFl : rwZ ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwZ : lFl ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lDh : rwZ ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwZ : lDh ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lDt : rwZ ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwZ : lDt ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lDg : rwZ ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwZ : lDg ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lDi : rwZ ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwZ : lDi ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lRp : rwZ ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwZ : lRp ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lRn : rwZ ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwZ : lRn ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lFle : rwZ ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwZ : lFle ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lKb : rwZ ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwZ : lKb ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lDir : rwZ ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwZ : lDir ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lFln : rwZ ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwZ : lFln ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lFll : rwZ ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwZ : lFll ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_lFls : rwZ ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwZ : lFls ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_kFu : rwZ ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwZ : kFu ≠ rwZ := by decide
@[simp] theorem prw_rwZ_ne_kD : rwZ ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwZ : kD ≠ rwZ := by decide
@[simp] theorem prw_rwA_ne_rwH : rwA ≠ rwH := by decide
@[simp] theorem prw_rwA_ne_rwE : rwA ≠ rwE := by decide
@[simp] theorem prw_rwA_ne_rwU : rwA ≠ rwU := by decide
@[simp] theorem prw_rwA_ne_rwZ : rwA ≠ rwZ := by decide
@[simp] theorem prw_rwA_ne_rwR : rwA ≠ rwR := by decide
@[simp] theorem prw_rwA_ne_lFl : rwA ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwA : lFl ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lDh : rwA ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwA : lDh ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lDt : rwA ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwA : lDt ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lDg : rwA ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwA : lDg ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lDi : rwA ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwA : lDi ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lRp : rwA ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwA : lRp ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lRn : rwA ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwA : lRn ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lFle : rwA ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwA : lFle ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lKb : rwA ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwA : lKb ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lDir : rwA ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwA : lDir ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lFln : rwA ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwA : lFln ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lFll : rwA ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwA : lFll ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_lFls : rwA ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwA : lFls ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_kFu : rwA ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwA : kFu ≠ rwA := by decide
@[simp] theorem prw_rwA_ne_kD : rwA ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwA : kD ≠ rwA := by decide
@[simp] theorem prw_rwR_ne_rwH : rwR ≠ rwH := by decide
@[simp] theorem prw_rwR_ne_rwE : rwR ≠ rwE := by decide
@[simp] theorem prw_rwR_ne_rwU : rwR ≠ rwU := by decide
@[simp] theorem prw_rwR_ne_rwZ : rwR ≠ rwZ := by decide
@[simp] theorem prw_rwR_ne_rwA : rwR ≠ rwA := by decide
@[simp] theorem prw_rwR_ne_lFl : rwR ≠ lFl := by decide
@[simp] theorem prw_lFl_ne_rwR : lFl ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lDh : rwR ≠ lDh := by decide
@[simp] theorem prw_lDh_ne_rwR : lDh ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lDt : rwR ≠ lDt := by decide
@[simp] theorem prw_lDt_ne_rwR : lDt ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lDg : rwR ≠ lDg := by decide
@[simp] theorem prw_lDg_ne_rwR : lDg ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lDi : rwR ≠ lDi := by decide
@[simp] theorem prw_lDi_ne_rwR : lDi ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lRp : rwR ≠ lRp := by decide
@[simp] theorem prw_lRp_ne_rwR : lRp ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lRn : rwR ≠ lRn := by decide
@[simp] theorem prw_lRn_ne_rwR : lRn ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lFle : rwR ≠ lFle := by decide
@[simp] theorem prw_lFle_ne_rwR : lFle ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lKb : rwR ≠ lKb := by decide
@[simp] theorem prw_lKb_ne_rwR : lKb ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lDir : rwR ≠ lDir := by decide
@[simp] theorem prw_lDir_ne_rwR : lDir ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lFln : rwR ≠ lFln := by decide
@[simp] theorem prw_lFln_ne_rwR : lFln ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lFll : rwR ≠ lFll := by decide
@[simp] theorem prw_lFll_ne_rwR : lFll ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_lFls : rwR ≠ lFls := by decide
@[simp] theorem prw_lFls_ne_rwR : lFls ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_kFu : rwR ≠ kFu := by decide
@[simp] theorem prw_kFu_ne_rwR : kFu ≠ rwR := by decide
@[simp] theorem prw_rwR_ne_kD : rwR ≠ kD := by decide
@[simp] theorem prw_kD_ne_rwR : kD ≠ rwR := by decide

def rwParams : List MlS := [rwH]
def rwLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, rwE, rwU, rwZ, rwA, rwR]
def rwBody (C : Ctx) : ProgHOL 64 := prologue rwLocals (.ite (.cmp .equal (vv rwH) (.const 0)) (.return (.const 0)) (.seq (.assign .local rwE (.op .sub [(vv rwH), (.const 1)])) (.ite (tagIsE rwE 2) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv rwE)) (.seq eViewP (.seq (.assign .local rwU (.load .one (vv lRp))) (.seq (.call (some (some (.local, rwZ), none)) fNz0 [(vv rwU)]) (.ite (vv rwZ) (.return (.const 1)) (allocP C rwA (.const 8) (.seq (.store (vv rwA) (.const 0)) (.seq (.call (some (some (.local, rwR), none)) fZc [(vv rwU), (vv rwA)]) (.return (vv rwR))))))))))) (.return (.const 0)))))

structure RwCodes (C : Ctx) : Prop where
  nz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)
  zc : ZcCodes C

section
variable {σ : Type}

def optPW (C : Ctx) (H : List (BitVec 64)) (s : AState) : Option ConLeche.PropWhen → BitVec 64 → Prop
  | none, w => w = 0
  | some pw, w => pwEnc C H s pw w

def PostOPW (C : Ctx) (s : AState) (r : Option ConLeche.PropWhen) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ H', C.H <+: H' ∧ optPW C H' s r w ∧ SR (ctxH C H') s st

theorem postOPW_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOPW C s a w s' st → PostOPW C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', h2, h3, h4⟩ => ⟨h1, H', h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem rw_spec (C : Ctx) (hok : CtxOK C) (hc : RwCodes C) (s : AState) (hwf : LStoreWF s.store.ls) :
    ∀ (H : List (BitVec 64)) (r : Option EIdx), C.H <+: H →
      (∀ h u, r = some h → s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l) →
      SpecR (σ := σ) (Pre (ctxH C H) s (rwParams.zip [optW r])) (rwBody C) s (residualPW r) (PostOPW (ctxH C H) s) := by
  intro H r hpH hden
  refine specR_prologue (postOPW_locals _ s) (Knot.params_none _ rwLocals rwParams _ (by decide) (by decide)) ?_
  rcases r with _ | h
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rwParams, ctxEnv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [residualPW]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rwParams, ctxEnv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne h) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI rwE _ (Enc.idxW h) (by decide) (by simp +decide [sev, Env.get, rwParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rw [residualPW]
  refine Knot.specR_tagIteV rwE h 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (h.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [ite_eq_left (show (h.tag == ETag.sort) = true by simp [htg, ETag.sort])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv rwE) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn _ => ?_)
  have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
  obtain ⟨u, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
  have hvs : s.store.viewSort h = some u := viewSort_of_view (by rw [htg]; rfl) hv
  refine specR_runBind (show ConRon.Arena.viewSort h s = .ok (some u, s) by show Except.ok (s.store.viewSort h, s) = _; rw [hvs]) ?_
  dsimp only
  obtain ⟨l, hl⟩ := hden h u rfl hv
  refine specR_runBind (show ConRon.Arena.readLevel u s = .ok (l, s) by simp [ConRon.Arena.readLevel, hl, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]) ?_
  refine specR_loadI' rwU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
  refine specR_dropM ?_
  refine specR_callPure (C := ctxH C H) rwZ fNz0 [nzU] [vv rwU] nzBody [Enc.idxW u] (nz l)
    (by decide) rfl (by decide) hc.nz ⟨by simp, trivial⟩ (PostBS (ctxH C H) s) (fun b w _ H' => H' = H ∧ w = boolW b)
    (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [nzU] _ rfl hlk) (nz0_spec (ctxH C H) hc.nz s hwf l u hl))
    (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
  subst H1; subst hw
  cases hz : nz l
  swap
  · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [zof_never _ hz]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  rw [zof_eq _ hz]
  refine specR_emptyBlk (C0 := C) hok (H := H) rwA (by decide) (fun H2 oe hp2 hbe => ?_)
  refine specR_callPure (C := ctxH C H2) rwR fZc zcParams [vv rwU, vv rwA] zcBody [Enc.idxW u, cellA C oe] (zps l)
    (by decide) rfl (by decide) hc.zc.self ⟨by simp, by simp <;> rfl, trivial⟩ (PostZc (ctxH C H2) s [])
    (fun r w _ H' => ∃ o ns, w = cellA C o ∧ BlkAt H' o (([] ++ ns).map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some r)
    (fun r w s' st ⟨hs, H', o, ns, hp, hw, hb, hdn, hsr⟩ => ⟨H', hp, ⟨o, ns, hw, hb, hdn⟩, by rw [hs]; exact hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu zcParams _ rfl hlk)
      (zc_spec C hok hc.zc s hwf l u H2 [] oe (hpH.trans hp2) hl (by simpa using hbe)))
    (fun w H3 hp3 ⟨o3, ns3, hw, hb3, hdn3⟩ => ?_)
  subst hw
  exact specR_returnI _ (cellA C o3) (by simp <;> rfl) (fun t ht => ⟨rfl, H3, hp2.trans hp3, ⟨o3, ns3, rfl, by simpa using hb3, hdn3⟩,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
