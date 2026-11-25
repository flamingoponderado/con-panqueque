import ConPanqueque.T.Core.WhnfApp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfCoreStepApp`: the batched β spine

The spine (`getAppSpine`), its head normalized once (`whnfCore`), the head and arguments of the result
(`headAndArgs`), and the walk (`whnfApp`) from argument `0`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem spine_sizes : ∀ (fuel : Nat) (h : EIdx) (s s' : AState) (t : EIdx × Array EIdx × Array EIdx),
    getAppSpineGo fuel h s = .ok (t, s') → t.2.1.size = t.2.2.size := by
  intro fuel
  induction fuel with
  | zero => intro h s s' t hr; simp [getAppSpineGo, fail, throw, throwThe, MonadExceptOf.throw, StateT.lift] at hr
  | succ f ih =>
    intro h s s' t hr
    rw [getAppSpineGo_succ] at hr
    split at hr
    · cases hv : s.store.viewApp h with
      | none =>
        simp [bind, StateT.bind, viewApp_run, hv, Except.bind, failDanglingE, fail, throwThe,
          MonadExceptOf.throw, StateT.lift] at hr
      | some fa =>
        obtain ⟨fn, a⟩ := fa
        cases hg : getAppSpineGo f fn s with
        | error e => simp [bind, StateT.bind, viewApp_run, hv, hg, Except.bind] at hr
        | ok p =>
          obtain ⟨t', s1⟩ := p
          simp [bind, StateT.bind, viewApp_run, hv, hg, Except.bind, pure, StateT.pure, Except.pure] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [ih fn s s1 t' hg]
    · simp [pure, StateT.pure, Except.pure] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rfl


def sPp := ofString "wsap"
def sH0 := ofString "wsah"
def sA := ofString "wsaa"
def sNd := ofString "wsan"
def sV := ofString "wsav"
def sSm := ofString "wsas"
def sHd := ofString "wsahd"
def sVa := ofString "wsava"
def sN2 := ofString "wsan2"
def sX := ofString "wsax"

@[simp] theorem wsa_sP_ne_sH0 : sPp ≠ sH0 := by decide
@[simp] theorem wsa_sP_ne_sA : sPp ≠ sA := by decide
@[simp] theorem wsa_sP_ne_sNd : sPp ≠ sNd := by decide
@[simp] theorem wsa_sP_ne_sV : sPp ≠ sV := by decide
@[simp] theorem wsa_sP_ne_sSm : sPp ≠ sSm := by decide
@[simp] theorem wsa_sP_ne_sHd : sPp ≠ sHd := by decide
@[simp] theorem wsa_sP_ne_sVa : sPp ≠ sVa := by decide
@[simp] theorem wsa_sP_ne_sN2 : sPp ≠ sN2 := by decide
@[simp] theorem wsa_sP_ne_sX : sPp ≠ sX := by decide
@[simp] theorem wsa_sP_ne_kFu : sPp ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sP : kFu ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_kC : sPp ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sP : kC ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_kD : sPp ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sP : kD ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_sE : sPp ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sP : sE ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_lFle : sPp ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sP : lFle ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_lDir : sPp ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sP : lDir ≠ sPp := by decide
@[simp] theorem wsa_sP_ne_lKb : sPp ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sP : lKb ≠ sPp := by decide
@[simp] theorem wsa_sH0_ne_sP : sH0 ≠ sPp := by decide
@[simp] theorem wsa_sH0_ne_sA : sH0 ≠ sA := by decide
@[simp] theorem wsa_sH0_ne_sNd : sH0 ≠ sNd := by decide
@[simp] theorem wsa_sH0_ne_sV : sH0 ≠ sV := by decide
@[simp] theorem wsa_sH0_ne_sSm : sH0 ≠ sSm := by decide
@[simp] theorem wsa_sH0_ne_sHd : sH0 ≠ sHd := by decide
@[simp] theorem wsa_sH0_ne_sVa : sH0 ≠ sVa := by decide
@[simp] theorem wsa_sH0_ne_sN2 : sH0 ≠ sN2 := by decide
@[simp] theorem wsa_sH0_ne_sX : sH0 ≠ sX := by decide
@[simp] theorem wsa_sH0_ne_kFu : sH0 ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sH0 : kFu ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_kC : sH0 ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sH0 : kC ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_kD : sH0 ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sH0 : kD ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_sE : sH0 ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sH0 : sE ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_lFle : sH0 ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sH0 : lFle ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_lDir : sH0 ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sH0 : lDir ≠ sH0 := by decide
@[simp] theorem wsa_sH0_ne_lKb : sH0 ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sH0 : lKb ≠ sH0 := by decide
@[simp] theorem wsa_sA_ne_sP : sA ≠ sPp := by decide
@[simp] theorem wsa_sA_ne_sH0 : sA ≠ sH0 := by decide
@[simp] theorem wsa_sA_ne_sNd : sA ≠ sNd := by decide
@[simp] theorem wsa_sA_ne_sV : sA ≠ sV := by decide
@[simp] theorem wsa_sA_ne_sSm : sA ≠ sSm := by decide
@[simp] theorem wsa_sA_ne_sHd : sA ≠ sHd := by decide
@[simp] theorem wsa_sA_ne_sVa : sA ≠ sVa := by decide
@[simp] theorem wsa_sA_ne_sN2 : sA ≠ sN2 := by decide
@[simp] theorem wsa_sA_ne_sX : sA ≠ sX := by decide
@[simp] theorem wsa_sA_ne_kFu : sA ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sA : kFu ≠ sA := by decide
@[simp] theorem wsa_sA_ne_kC : sA ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sA : kC ≠ sA := by decide
@[simp] theorem wsa_sA_ne_kD : sA ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sA : kD ≠ sA := by decide
@[simp] theorem wsa_sA_ne_sE : sA ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sA : sE ≠ sA := by decide
@[simp] theorem wsa_sA_ne_lFle : sA ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sA : lFle ≠ sA := by decide
@[simp] theorem wsa_sA_ne_lDir : sA ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sA : lDir ≠ sA := by decide
@[simp] theorem wsa_sA_ne_lKb : sA ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sA : lKb ≠ sA := by decide
@[simp] theorem wsa_sNd_ne_sP : sNd ≠ sPp := by decide
@[simp] theorem wsa_sNd_ne_sH0 : sNd ≠ sH0 := by decide
@[simp] theorem wsa_sNd_ne_sA : sNd ≠ sA := by decide
@[simp] theorem wsa_sNd_ne_sV : sNd ≠ sV := by decide
@[simp] theorem wsa_sNd_ne_sSm : sNd ≠ sSm := by decide
@[simp] theorem wsa_sNd_ne_sHd : sNd ≠ sHd := by decide
@[simp] theorem wsa_sNd_ne_sVa : sNd ≠ sVa := by decide
@[simp] theorem wsa_sNd_ne_sN2 : sNd ≠ sN2 := by decide
@[simp] theorem wsa_sNd_ne_sX : sNd ≠ sX := by decide
@[simp] theorem wsa_sNd_ne_kFu : sNd ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sNd : kFu ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_kC : sNd ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sNd : kC ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_kD : sNd ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sNd : kD ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_sE : sNd ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sNd : sE ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_lFle : sNd ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sNd : lFle ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_lDir : sNd ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sNd : lDir ≠ sNd := by decide
@[simp] theorem wsa_sNd_ne_lKb : sNd ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sNd : lKb ≠ sNd := by decide
@[simp] theorem wsa_sV_ne_sP : sV ≠ sPp := by decide
@[simp] theorem wsa_sV_ne_sH0 : sV ≠ sH0 := by decide
@[simp] theorem wsa_sV_ne_sA : sV ≠ sA := by decide
@[simp] theorem wsa_sV_ne_sNd : sV ≠ sNd := by decide
@[simp] theorem wsa_sV_ne_sSm : sV ≠ sSm := by decide
@[simp] theorem wsa_sV_ne_sHd : sV ≠ sHd := by decide
@[simp] theorem wsa_sV_ne_sVa : sV ≠ sVa := by decide
@[simp] theorem wsa_sV_ne_sN2 : sV ≠ sN2 := by decide
@[simp] theorem wsa_sV_ne_sX : sV ≠ sX := by decide
@[simp] theorem wsa_sV_ne_kFu : sV ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sV : kFu ≠ sV := by decide
@[simp] theorem wsa_sV_ne_kC : sV ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sV : kC ≠ sV := by decide
@[simp] theorem wsa_sV_ne_kD : sV ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sV : kD ≠ sV := by decide
@[simp] theorem wsa_sV_ne_sE : sV ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sV : sE ≠ sV := by decide
@[simp] theorem wsa_sV_ne_lFle : sV ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sV : lFle ≠ sV := by decide
@[simp] theorem wsa_sV_ne_lDir : sV ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sV : lDir ≠ sV := by decide
@[simp] theorem wsa_sV_ne_lKb : sV ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sV : lKb ≠ sV := by decide
@[simp] theorem wsa_sSm_ne_sP : sSm ≠ sPp := by decide
@[simp] theorem wsa_sSm_ne_sH0 : sSm ≠ sH0 := by decide
@[simp] theorem wsa_sSm_ne_sA : sSm ≠ sA := by decide
@[simp] theorem wsa_sSm_ne_sNd : sSm ≠ sNd := by decide
@[simp] theorem wsa_sSm_ne_sV : sSm ≠ sV := by decide
@[simp] theorem wsa_sSm_ne_sHd : sSm ≠ sHd := by decide
@[simp] theorem wsa_sSm_ne_sVa : sSm ≠ sVa := by decide
@[simp] theorem wsa_sSm_ne_sN2 : sSm ≠ sN2 := by decide
@[simp] theorem wsa_sSm_ne_sX : sSm ≠ sX := by decide
@[simp] theorem wsa_sSm_ne_kFu : sSm ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sSm : kFu ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_kC : sSm ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sSm : kC ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_kD : sSm ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sSm : kD ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_sE : sSm ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sSm : sE ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_lFle : sSm ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sSm : lFle ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_lDir : sSm ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sSm : lDir ≠ sSm := by decide
@[simp] theorem wsa_sSm_ne_lKb : sSm ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sSm : lKb ≠ sSm := by decide
@[simp] theorem wsa_sHd_ne_sP : sHd ≠ sPp := by decide
@[simp] theorem wsa_sHd_ne_sH0 : sHd ≠ sH0 := by decide
@[simp] theorem wsa_sHd_ne_sA : sHd ≠ sA := by decide
@[simp] theorem wsa_sHd_ne_sNd : sHd ≠ sNd := by decide
@[simp] theorem wsa_sHd_ne_sV : sHd ≠ sV := by decide
@[simp] theorem wsa_sHd_ne_sSm : sHd ≠ sSm := by decide
@[simp] theorem wsa_sHd_ne_sVa : sHd ≠ sVa := by decide
@[simp] theorem wsa_sHd_ne_sN2 : sHd ≠ sN2 := by decide
@[simp] theorem wsa_sHd_ne_sX : sHd ≠ sX := by decide
@[simp] theorem wsa_sHd_ne_kFu : sHd ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sHd : kFu ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_kC : sHd ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sHd : kC ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_kD : sHd ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sHd : kD ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_sE : sHd ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sHd : sE ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_lFle : sHd ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sHd : lFle ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_lDir : sHd ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sHd : lDir ≠ sHd := by decide
@[simp] theorem wsa_sHd_ne_lKb : sHd ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sHd : lKb ≠ sHd := by decide
@[simp] theorem wsa_sVa_ne_sP : sVa ≠ sPp := by decide
@[simp] theorem wsa_sVa_ne_sH0 : sVa ≠ sH0 := by decide
@[simp] theorem wsa_sVa_ne_sA : sVa ≠ sA := by decide
@[simp] theorem wsa_sVa_ne_sNd : sVa ≠ sNd := by decide
@[simp] theorem wsa_sVa_ne_sV : sVa ≠ sV := by decide
@[simp] theorem wsa_sVa_ne_sSm : sVa ≠ sSm := by decide
@[simp] theorem wsa_sVa_ne_sHd : sVa ≠ sHd := by decide
@[simp] theorem wsa_sVa_ne_sN2 : sVa ≠ sN2 := by decide
@[simp] theorem wsa_sVa_ne_sX : sVa ≠ sX := by decide
@[simp] theorem wsa_sVa_ne_kFu : sVa ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sVa : kFu ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_kC : sVa ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sVa : kC ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_kD : sVa ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sVa : kD ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_sE : sVa ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sVa : sE ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_lFle : sVa ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sVa : lFle ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_lDir : sVa ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sVa : lDir ≠ sVa := by decide
@[simp] theorem wsa_sVa_ne_lKb : sVa ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sVa : lKb ≠ sVa := by decide
@[simp] theorem wsa_sN2_ne_sP : sN2 ≠ sPp := by decide
@[simp] theorem wsa_sN2_ne_sH0 : sN2 ≠ sH0 := by decide
@[simp] theorem wsa_sN2_ne_sA : sN2 ≠ sA := by decide
@[simp] theorem wsa_sN2_ne_sNd : sN2 ≠ sNd := by decide
@[simp] theorem wsa_sN2_ne_sV : sN2 ≠ sV := by decide
@[simp] theorem wsa_sN2_ne_sSm : sN2 ≠ sSm := by decide
@[simp] theorem wsa_sN2_ne_sHd : sN2 ≠ sHd := by decide
@[simp] theorem wsa_sN2_ne_sVa : sN2 ≠ sVa := by decide
@[simp] theorem wsa_sN2_ne_sX : sN2 ≠ sX := by decide
@[simp] theorem wsa_sN2_ne_kFu : sN2 ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sN2 : kFu ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_kC : sN2 ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sN2 : kC ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_kD : sN2 ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sN2 : kD ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_sE : sN2 ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sN2 : sE ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_lFle : sN2 ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sN2 : lFle ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_lDir : sN2 ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sN2 : lDir ≠ sN2 := by decide
@[simp] theorem wsa_sN2_ne_lKb : sN2 ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sN2 : lKb ≠ sN2 := by decide
@[simp] theorem wsa_sX_ne_sP : sX ≠ sPp := by decide
@[simp] theorem wsa_sX_ne_sH0 : sX ≠ sH0 := by decide
@[simp] theorem wsa_sX_ne_sA : sX ≠ sA := by decide
@[simp] theorem wsa_sX_ne_sNd : sX ≠ sNd := by decide
@[simp] theorem wsa_sX_ne_sV : sX ≠ sV := by decide
@[simp] theorem wsa_sX_ne_sSm : sX ≠ sSm := by decide
@[simp] theorem wsa_sX_ne_sHd : sX ≠ sHd := by decide
@[simp] theorem wsa_sX_ne_sVa : sX ≠ sVa := by decide
@[simp] theorem wsa_sX_ne_sN2 : sX ≠ sN2 := by decide
@[simp] theorem wsa_sX_ne_kFu : sX ≠ kFu := by decide
@[simp] theorem wsa_kFu_ne_sX : kFu ≠ sX := by decide
@[simp] theorem wsa_sX_ne_kC : sX ≠ kC := by decide
@[simp] theorem wsa_kC_ne_sX : kC ≠ sX := by decide
@[simp] theorem wsa_sX_ne_kD : sX ≠ kD := by decide
@[simp] theorem wsa_kD_ne_sX : kD ≠ sX := by decide
@[simp] theorem wsa_sX_ne_sE : sX ≠ sE := by decide
@[simp] theorem wsa_sE_ne_sX : sE ≠ sX := by decide
@[simp] theorem wsa_sX_ne_lFle : sX ≠ lFle := by decide
@[simp] theorem wsa_lFle_ne_sX : lFle ≠ sX := by decide
@[simp] theorem wsa_sX_ne_lDir : sX ≠ lDir := by decide
@[simp] theorem wsa_lDir_ne_sX : lDir ≠ sX := by decide
@[simp] theorem wsa_sX_ne_lKb : sX ≠ lKb := by decide
@[simp] theorem wsa_lKb_ne_sX : lKb ≠ sX := by decide

def wsaLocals : List MlS := [sPp, sH0, sA, sNd, sV, sSm, sHd, sVa, sN2, sX]

def wsaRest : ProgHOL 64 :=
  .seq (.assign .local sN2 (.load .one (vv sA)))
  (.seq (.call (some (some (.local, sX), none)) fWap
    [vv kFu, vv kD, vv sV, vv sHd, vv sVa, vv sSm, vv sA, vv sNd, .const 0, vv sN2]) (.return (vv sX)))

def wsaCore (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, sPp), none)) fGsp [.const (BitVec.ofNat 64 coreWalkFuel), vv sE])
  (.seq (.assign .local sH0 (.load .one (vv sPp)))
  (.seq (.assign .local sA (.load .one (.op .add [vv sPp, .const 8])))
  (.seq (.assign .local sNd (.load .one (.op .add [vv sPp, .const 16])))
  (.seq (.call (some (some (.local, sV), none)) fWC [vv kFu, vv kC, vv kD, vv sH0])
  (.seq (.assign .local sSm (.cmp .equal (vv sV) (vv sH0)))
  (.ite (tagIs4E sV)
    (.seq (.call (some (some (.local, sHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv sV])
    (.seq (.call (some (some (.local, sVa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv sV])
      wsaRest))
    (.seq (.assign .local sHd (vv sV)) (allocP C sVa (.const 8) (.seq (.store (vv sVa) (.const 0)) wsaRest)))))))))

def wsaBody (C : Ctx) : ProgHOL 64 := prologue wsaLocals (wsaCore C)


section
variable {σ : Type}

theorem wsa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wsaLocals → (ctxEnv C ++ apParams.zip vals).get x = none :=
  Knot.params_none C wsaLocals apParams vals (by decide) (by decide)

theorem wsa_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fGsp = some (gspParams.map (fun p => (p, ShapeHOL.one)), gspBody C, .one))
    (hca : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one))
    (hcwc : C.code.lookup fWC = some (pmap wcParams, wcE, .one))
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcg : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one))
    (hcwap : C.code.lookup fWap = some (wapParams.map (fun p => (p, ShapeHOL.one)), wapBody C, .one))
    (s : AState) (cheap : Bool) (d : Nat) (e : EIdx)
    (hWC : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e'] wcE s1
      ((knot mode C n).whnfCore cheap d e') (PostK (ctxH C H)))
    (hWap : ∀ (H : List (BitVec 64)) s1 v hd (va args nodes : Array EIdx) ov oa on same, C.H <+: H →
      BlkAt H ov (va.toList.map Enc.idxW) → BlkAt H oa (args.toList.map Enc.idxW) →
      BlkAt H on (nodes.toList.map Enc.idxW) → nodes.size = args.size → va.size < 2 ^ 58 → args.size < 2 ^ 58 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (wapParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW v,
        Enc.idxW hd, cellA C ov, boolW same, cellA C oa, cellA C on, BitVec.ofNat 64 0, BitVec.ofNat 64 args.size]))
        (wapBody C) s1 (whnfApp mode (knot mode C n) C.fe d v hd va same args nodes 0) (PostWS (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (apParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e])) (wsaBody C)
      s (whnfCoreStepApp mode (knot mode C n) C.fe cheap d e) (PostWS C) := by
  refine specR_prologue (postWS_locals C) (wsa_none C _) ?_
  unfold wsaCore whnfCoreStepApp getAppSpine
  refine specR_callNIH sPp fGsp gspParams [.const (BitVec.ofNat 64 coreWalkFuel), vv sE] (gspBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcs
    ⟨rfl, by simp +decide [sev, Env.get, apParams, ctxEnv], trivial⟩
    (fun r w s' st => getAppSpineGo coreWalkFuel e s = .ok (r, s') ∧ PostSp C s r w s' st)
    (fun r w s' H' => getAppSpineGo coreWalkFuel e s = .ok (r, s') ∧ s' = s ∧ ∃ o pa pn, w = cellA C o ∧
      H'[o]? = some (Enc.idxW r.1) ∧ H'[o + 1]? = some (cellA C pa) ∧ H'[o + 2]? = some (cellA C pn) ∧
      BlkAt H' pa (r.2.1.toList.map Enc.idxW) ∧ BlkAt H' pn (r.2.2.toList.map Enc.idxW))
    (fun r w s' st ⟨hrun, hs, H', o, pa, pn, hp, hw, h0, h1, h2, hba, hbn, hsr⟩ =>
      ⟨H', hp, ⟨hrun, hs, o, pa, pn, hw, h0, h1, h2, hba, hbn⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu gspParams _ rfl hlk)
      (gsp_spec C hok hcs hca coreWalkFuel CV.coreWalkFuel_lt C.H s e (List.prefix_refl _))))
    (fun sp w s1 H1 hp1 ⟨hrun, hs, o, pa, pn, hw, h0, h1, h2, hba, hbn⟩ => ?_)
  subst s1 hw
  have hsz := spine_sizes coreWalkFuel e s s sp hrun
  refine UD.specR_heapLoadI' (C := ctxH C H1) sH0 (vv sPp) o _ h0 (by decide) (by simp; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) sA _ (o + 1) _ h1 (by decide) (by simp [sev]; exact cellA_add8 C o) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) sNd _ (o + 2) _ h2 (by decide)
    (by simp [sev]; rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl]; exact ExPre.cellA_off C _ 2) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsa := blk_small0 (C := ctxH C H1) (ctxOK_H hok _) ht0.sr hba
  simp only [List.length_map, Array.length_toList] at hsa
  refine Big.specR_callKC (C := ctxH C H1) sV fWC wcParams [vv kFu, vv kC, vv kD, vv sH0] wcE
    [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW sp.1] (by decide) rfl (by decide) hcwc
    ⟨by simp +decide [Env.get, apParams, ctxEnv], by simp +decide [Env.get, apParams, ctxEnv],
      by simp +decide [Env.get, apParams, ctxEnv], by simp, trivial⟩ (hWC H1 s hp1 sp.1)
    (fun v s2 H2 hp2 _ => ?_)
  have heqb : ∀ Γ : Env, Γ.get sV = some (Enc.idxW v) → Γ.get sH0 = some (Enc.idxW sp.1) →
      sev Γ (.cmp .equal (vv sV) (vv sH0)) = some (boolW (v == sp.1)) := by
    intro Γ h1 h2
    simp only [sev, sev_vv, h1, h2]
    by_cases he : v = sp.1
    · rw [he]; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : Enc.idxW v ≠ Enc.idxW sp.1 := fun x => he (Enc.idxW_inj x)
      simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, he]
  refine specR_assignI sSm _ (boolW (v == sp.1)) (by decide) (heqb _ (by simp) (by simp)) ?_
  have hT := sev_tagIs4B ((sSm, boolW (v == sp.1)) :: (sV, Enc.idxW v) :: (sNd, cellA C pn) :: (sA, cellA C pa) ::
    (sH0, Enc.idxW sp.1) :: (sPp, cellA C o) ::
    (ctxEnv C ++ apParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e])) sV v (by simp)
  have hpall : C.H <+: H2 := hp1.trans hp2
  unfold headAndArgs
  by_cases ht : (v.tag == 4) = true
  · rw [ite_eq_left (show (v.tag == ETag.app) = true from ht)]
    simp only [bind_assoc, pure_bind]
    refine specR_ifI _ 1 (by rw [hT, ht]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_callNIM (C := ctxH C H2) sHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv sV]
      getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW v] (by decide) rfl (by decide) hcaf
      ⟨rfl, by simp, trivial⟩
      (fun a w s' st => getAppFn coreWalkFuel v s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
      (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H2) hcaf coreWalkFuel v s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
          hlk 1 (by decide)⟩))
      (fun hd w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s2 = s' := hs.symm
    subst hs'
    refine specR_callNIH (C := ctxH C H2) sVa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv sV]
      (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW v] (by decide) rfl (by decide) hcg
      ⟨rfl, by simp, trivial⟩
      (PostA (ctxH C H2)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
      (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec (ctxH C H2) (ctxOK_H hok _) hcg coreWalkFuel CV.coreWalkFuel_lt H2 v s2))
      (fun va w s3 H3 hp3 ⟨o3, hw, hb3⟩ => ?_)
    subst hw
    refine specR_atEntry fun t1 ht1 => ?_
    have hsv := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht1.sr hb3
    simp only [List.length_map] at hsv
    have hpa3 : H1 <+: H3 := hp2.trans hp3
    obtain ⟨hlo, hlv⟩ := blkAt_get0 (blkAt_mono hba hpa3)
    have hw0 : (ctxH C H3).H[pa]? = some (BitVec.ofNat 64 sp.2.1.size) := by
      show H3[pa]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
    unfold wsaRest
    refine UD.specR_heapLoadI' (C := ctxH C H3) sN2 (vv sA) pa _ hw0 (by decide) (by simp; rfl) ?_
    refine specR_mono (R := PostWS (ctxH C H3)) ?_ (fun _ h => h) (fun a w s' t ⟨H', hp', hw', hsr'⟩ =>
      ⟨H', hpall.trans (hp3.trans hp'), hw', hsr'⟩)
    exact specR_callWS (D := ctxLocals ++ wsaLocals) sX fWap wapParams
      [vv kFu, vv kD, vv sV, vv sHd, vv sVa, vv sSm, vv sA, vv sNd, .const 0, vv sN2] (wapBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW v, Enc.idxW hd, cellA C o3, boolW (v == sp.1), cellA C pa,
        cellA C pn, BitVec.ofNat 64 0, BitVec.ofNat 64 sp.2.1.size] (by decide) rfl (by decide) hcwap
      ⟨by simp +decide [Env.get, apParams, ctxEnv], by simp +decide [Env.get, apParams, ctxEnv], by simp, by simp,
        by simp, by simp, by simp, by simp, rfl, by simp, trivial⟩
      (hWap H3 s3 v hd va.toArray sp.2.1 sp.2.2 o3 pa pn (v == sp.1) (hpall.trans hp3) (by simpa using hb3)
        (blkAt_mono hba hpa3) (blkAt_mono hbn hpa3) hsz.symm (by simpa using hsv) hsa)
  · rw [ite_eq_right (show ¬ (v.tag == ETag.app) = true from ht)]
    refine specR_ifI _ 0 (by rw [hT]; simp [ht, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI sHd (vv sV) (Enc.idxW v) (by decide) (by simp) ?_
    rw [pure_bind]
    refine specR_emptyBlk (C0 := C) (H := H2) hok sVa (by decide) (fun H3 o3 hp3 hb3 => ?_)
    have hpa3 : H1 <+: H3 := hp2.trans hp3
    obtain ⟨hlo, hlv⟩ := blkAt_get0 (blkAt_mono hba hpa3)
    have hw0 : (ctxH C H3).H[pa]? = some (BitVec.ofNat 64 sp.2.1.size) := by
      show H3[pa]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
    unfold wsaRest
    refine UD.specR_heapLoadI' (C := ctxH C H3) sN2 (vv sA) pa _ hw0 (by decide) (by simp; rfl) ?_
    refine specR_mono (R := PostWS (ctxH C H3)) ?_ (fun _ h => h) (fun a w s' t ⟨H', hp', hw', hsr'⟩ =>
      ⟨H', hpall.trans (hp3.trans hp'), hw', hsr'⟩)
    exact specR_callWS (D := ctxLocals ++ wsaLocals) sX fWap wapParams
      [vv kFu, vv kD, vv sV, vv sHd, vv sVa, vv sSm, vv sA, vv sNd, .const 0, vv sN2] (wapBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW v, Enc.idxW v, cellA C o3, boolW (v == sp.1), cellA C pa,
        cellA C pn, BitVec.ofNat 64 0, BitVec.ofNat 64 sp.2.1.size] (by decide) rfl (by decide) hcwap
      ⟨by simp +decide [Env.get, apParams, ctxEnv], by simp +decide [Env.get, apParams, ctxEnv], by simp, by simp,
        by simp, by simp, by simp, by simp, rfl, by simp, trivial⟩
      (hWap H3 s2 v v #[] sp.2.1 sp.2.2 o3 pa pn (v == sp.1) (hpall.trans hp3) (by simpa using hb3)
        (blkAt_mono hba hpa3) (blkAt_mono hbn hpa3) hsz.symm (by simp) hsa)

end

end ConPanqueque.T.WC
