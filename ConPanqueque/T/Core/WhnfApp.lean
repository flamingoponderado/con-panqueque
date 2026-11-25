import ConPanqueque.T.Core.AppIota
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfApp`: the β/ι walk over a spine

Over the spine's arguments: a λ head opens a peel group (`betaPeel`); a stuck head applies the argument (the
spine's own node when the head did not move), tries ι at the spine so far (`whnfAppIota`), and either a fired
reduct is applied to the rest, or the walk goes on. A recursive function over the argument index.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def yV := ofString "wav"
def yHd := ofString "wahd"
def yVa := ofString "wava"
def ySm := ofString "wasm"
def yAr := ofString "waar"
def yNd := ofString "wand"
def yI := ofString "wai2"
def yN := ofString "wan2"
def yA := ofString "waa"
def yNo := ofString "wano"
def yB := ofString "wab"
def yX := ofString "wax"
def yAp := ofString "waap"
def yS2 := ofString "was2"
def yVa2 := ofString "wava2"
def yK := ofString "wak"
def yO := ofString "wao"
def yE3 := ofString "wae3"
def fWap := ofString "whnfApp"

@[simp] theorem wy_yV_ne_yHd : yV ≠ yHd := by decide
@[simp] theorem wy_yV_ne_yVa : yV ≠ yVa := by decide
@[simp] theorem wy_yV_ne_ySm : yV ≠ ySm := by decide
@[simp] theorem wy_yV_ne_yAr : yV ≠ yAr := by decide
@[simp] theorem wy_yV_ne_yNd : yV ≠ yNd := by decide
@[simp] theorem wy_yV_ne_yI : yV ≠ yI := by decide
@[simp] theorem wy_yV_ne_yN : yV ≠ yN := by decide
@[simp] theorem wy_yV_ne_yA : yV ≠ yA := by decide
@[simp] theorem wy_yV_ne_yNo : yV ≠ yNo := by decide
@[simp] theorem wy_yV_ne_yB : yV ≠ yB := by decide
@[simp] theorem wy_yV_ne_yX : yV ≠ yX := by decide
@[simp] theorem wy_yV_ne_yAp : yV ≠ yAp := by decide
@[simp] theorem wy_yV_ne_yS2 : yV ≠ yS2 := by decide
@[simp] theorem wy_yV_ne_yVa2 : yV ≠ yVa2 := by decide
@[simp] theorem wy_yV_ne_yK : yV ≠ yK := by decide
@[simp] theorem wy_yV_ne_yO : yV ≠ yO := by decide
@[simp] theorem wy_yV_ne_yE3 : yV ≠ yE3 := by decide
@[simp] theorem wy_yV_ne_lFl : yV ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yV : lFl ≠ yV := by decide
@[simp] theorem wy_yV_ne_lDh : yV ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yV : lDh ≠ yV := by decide
@[simp] theorem wy_yV_ne_lDt : yV ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yV : lDt ≠ yV := by decide
@[simp] theorem wy_yV_ne_lDg : yV ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yV : lDg ≠ yV := by decide
@[simp] theorem wy_yV_ne_lDi : yV ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yV : lDi ≠ yV := by decide
@[simp] theorem wy_yV_ne_lRp : yV ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yV : lRp ≠ yV := by decide
@[simp] theorem wy_yV_ne_lRn : yV ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yV : lRn ≠ yV := by decide
@[simp] theorem wy_yV_ne_kFu : yV ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yV : kFu ≠ yV := by decide
@[simp] theorem wy_yV_ne_kD : yV ≠ kD := by decide
@[simp] theorem wy_kD_ne_yV : kD ≠ yV := by decide
@[simp] theorem wy_yV_ne_lFle : yV ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yV : lFle ≠ yV := by decide
@[simp] theorem wy_yV_ne_lDir : yV ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yV : lDir ≠ yV := by decide
@[simp] theorem wy_yV_ne_lKb : yV ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yV : lKb ≠ yV := by decide
@[simp] theorem wy_yHd_ne_yV : yHd ≠ yV := by decide
@[simp] theorem wy_yHd_ne_yVa : yHd ≠ yVa := by decide
@[simp] theorem wy_yHd_ne_ySm : yHd ≠ ySm := by decide
@[simp] theorem wy_yHd_ne_yAr : yHd ≠ yAr := by decide
@[simp] theorem wy_yHd_ne_yNd : yHd ≠ yNd := by decide
@[simp] theorem wy_yHd_ne_yI : yHd ≠ yI := by decide
@[simp] theorem wy_yHd_ne_yN : yHd ≠ yN := by decide
@[simp] theorem wy_yHd_ne_yA : yHd ≠ yA := by decide
@[simp] theorem wy_yHd_ne_yNo : yHd ≠ yNo := by decide
@[simp] theorem wy_yHd_ne_yB : yHd ≠ yB := by decide
@[simp] theorem wy_yHd_ne_yX : yHd ≠ yX := by decide
@[simp] theorem wy_yHd_ne_yAp : yHd ≠ yAp := by decide
@[simp] theorem wy_yHd_ne_yS2 : yHd ≠ yS2 := by decide
@[simp] theorem wy_yHd_ne_yVa2 : yHd ≠ yVa2 := by decide
@[simp] theorem wy_yHd_ne_yK : yHd ≠ yK := by decide
@[simp] theorem wy_yHd_ne_yO : yHd ≠ yO := by decide
@[simp] theorem wy_yHd_ne_yE3 : yHd ≠ yE3 := by decide
@[simp] theorem wy_yHd_ne_lFl : yHd ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yHd : lFl ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lDh : yHd ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yHd : lDh ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lDt : yHd ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yHd : lDt ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lDg : yHd ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yHd : lDg ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lDi : yHd ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yHd : lDi ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lRp : yHd ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yHd : lRp ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lRn : yHd ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yHd : lRn ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_kFu : yHd ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yHd : kFu ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_kD : yHd ≠ kD := by decide
@[simp] theorem wy_kD_ne_yHd : kD ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lFle : yHd ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yHd : lFle ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lDir : yHd ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yHd : lDir ≠ yHd := by decide
@[simp] theorem wy_yHd_ne_lKb : yHd ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yHd : lKb ≠ yHd := by decide
@[simp] theorem wy_yVa_ne_yV : yVa ≠ yV := by decide
@[simp] theorem wy_yVa_ne_yHd : yVa ≠ yHd := by decide
@[simp] theorem wy_yVa_ne_ySm : yVa ≠ ySm := by decide
@[simp] theorem wy_yVa_ne_yAr : yVa ≠ yAr := by decide
@[simp] theorem wy_yVa_ne_yNd : yVa ≠ yNd := by decide
@[simp] theorem wy_yVa_ne_yI : yVa ≠ yI := by decide
@[simp] theorem wy_yVa_ne_yN : yVa ≠ yN := by decide
@[simp] theorem wy_yVa_ne_yA : yVa ≠ yA := by decide
@[simp] theorem wy_yVa_ne_yNo : yVa ≠ yNo := by decide
@[simp] theorem wy_yVa_ne_yB : yVa ≠ yB := by decide
@[simp] theorem wy_yVa_ne_yX : yVa ≠ yX := by decide
@[simp] theorem wy_yVa_ne_yAp : yVa ≠ yAp := by decide
@[simp] theorem wy_yVa_ne_yS2 : yVa ≠ yS2 := by decide
@[simp] theorem wy_yVa_ne_yVa2 : yVa ≠ yVa2 := by decide
@[simp] theorem wy_yVa_ne_yK : yVa ≠ yK := by decide
@[simp] theorem wy_yVa_ne_yO : yVa ≠ yO := by decide
@[simp] theorem wy_yVa_ne_yE3 : yVa ≠ yE3 := by decide
@[simp] theorem wy_yVa_ne_lFl : yVa ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yVa : lFl ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lDh : yVa ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yVa : lDh ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lDt : yVa ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yVa : lDt ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lDg : yVa ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yVa : lDg ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lDi : yVa ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yVa : lDi ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lRp : yVa ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yVa : lRp ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lRn : yVa ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yVa : lRn ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_kFu : yVa ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yVa : kFu ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_kD : yVa ≠ kD := by decide
@[simp] theorem wy_kD_ne_yVa : kD ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lFle : yVa ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yVa : lFle ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lDir : yVa ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yVa : lDir ≠ yVa := by decide
@[simp] theorem wy_yVa_ne_lKb : yVa ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yVa : lKb ≠ yVa := by decide
@[simp] theorem wy_ySm_ne_yV : ySm ≠ yV := by decide
@[simp] theorem wy_ySm_ne_yHd : ySm ≠ yHd := by decide
@[simp] theorem wy_ySm_ne_yVa : ySm ≠ yVa := by decide
@[simp] theorem wy_ySm_ne_yAr : ySm ≠ yAr := by decide
@[simp] theorem wy_ySm_ne_yNd : ySm ≠ yNd := by decide
@[simp] theorem wy_ySm_ne_yI : ySm ≠ yI := by decide
@[simp] theorem wy_ySm_ne_yN : ySm ≠ yN := by decide
@[simp] theorem wy_ySm_ne_yA : ySm ≠ yA := by decide
@[simp] theorem wy_ySm_ne_yNo : ySm ≠ yNo := by decide
@[simp] theorem wy_ySm_ne_yB : ySm ≠ yB := by decide
@[simp] theorem wy_ySm_ne_yX : ySm ≠ yX := by decide
@[simp] theorem wy_ySm_ne_yAp : ySm ≠ yAp := by decide
@[simp] theorem wy_ySm_ne_yS2 : ySm ≠ yS2 := by decide
@[simp] theorem wy_ySm_ne_yVa2 : ySm ≠ yVa2 := by decide
@[simp] theorem wy_ySm_ne_yK : ySm ≠ yK := by decide
@[simp] theorem wy_ySm_ne_yO : ySm ≠ yO := by decide
@[simp] theorem wy_ySm_ne_yE3 : ySm ≠ yE3 := by decide
@[simp] theorem wy_ySm_ne_lFl : ySm ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_ySm : lFl ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lDh : ySm ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_ySm : lDh ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lDt : ySm ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_ySm : lDt ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lDg : ySm ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_ySm : lDg ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lDi : ySm ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_ySm : lDi ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lRp : ySm ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_ySm : lRp ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lRn : ySm ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_ySm : lRn ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_kFu : ySm ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_ySm : kFu ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_kD : ySm ≠ kD := by decide
@[simp] theorem wy_kD_ne_ySm : kD ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lFle : ySm ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_ySm : lFle ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lDir : ySm ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_ySm : lDir ≠ ySm := by decide
@[simp] theorem wy_ySm_ne_lKb : ySm ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_ySm : lKb ≠ ySm := by decide
@[simp] theorem wy_yAr_ne_yV : yAr ≠ yV := by decide
@[simp] theorem wy_yAr_ne_yHd : yAr ≠ yHd := by decide
@[simp] theorem wy_yAr_ne_yVa : yAr ≠ yVa := by decide
@[simp] theorem wy_yAr_ne_ySm : yAr ≠ ySm := by decide
@[simp] theorem wy_yAr_ne_yNd : yAr ≠ yNd := by decide
@[simp] theorem wy_yAr_ne_yI : yAr ≠ yI := by decide
@[simp] theorem wy_yAr_ne_yN : yAr ≠ yN := by decide
@[simp] theorem wy_yAr_ne_yA : yAr ≠ yA := by decide
@[simp] theorem wy_yAr_ne_yNo : yAr ≠ yNo := by decide
@[simp] theorem wy_yAr_ne_yB : yAr ≠ yB := by decide
@[simp] theorem wy_yAr_ne_yX : yAr ≠ yX := by decide
@[simp] theorem wy_yAr_ne_yAp : yAr ≠ yAp := by decide
@[simp] theorem wy_yAr_ne_yS2 : yAr ≠ yS2 := by decide
@[simp] theorem wy_yAr_ne_yVa2 : yAr ≠ yVa2 := by decide
@[simp] theorem wy_yAr_ne_yK : yAr ≠ yK := by decide
@[simp] theorem wy_yAr_ne_yO : yAr ≠ yO := by decide
@[simp] theorem wy_yAr_ne_yE3 : yAr ≠ yE3 := by decide
@[simp] theorem wy_yAr_ne_lFl : yAr ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yAr : lFl ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lDh : yAr ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yAr : lDh ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lDt : yAr ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yAr : lDt ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lDg : yAr ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yAr : lDg ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lDi : yAr ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yAr : lDi ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lRp : yAr ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yAr : lRp ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lRn : yAr ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yAr : lRn ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_kFu : yAr ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yAr : kFu ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_kD : yAr ≠ kD := by decide
@[simp] theorem wy_kD_ne_yAr : kD ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lFle : yAr ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yAr : lFle ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lDir : yAr ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yAr : lDir ≠ yAr := by decide
@[simp] theorem wy_yAr_ne_lKb : yAr ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yAr : lKb ≠ yAr := by decide
@[simp] theorem wy_yNd_ne_yV : yNd ≠ yV := by decide
@[simp] theorem wy_yNd_ne_yHd : yNd ≠ yHd := by decide
@[simp] theorem wy_yNd_ne_yVa : yNd ≠ yVa := by decide
@[simp] theorem wy_yNd_ne_ySm : yNd ≠ ySm := by decide
@[simp] theorem wy_yNd_ne_yAr : yNd ≠ yAr := by decide
@[simp] theorem wy_yNd_ne_yI : yNd ≠ yI := by decide
@[simp] theorem wy_yNd_ne_yN : yNd ≠ yN := by decide
@[simp] theorem wy_yNd_ne_yA : yNd ≠ yA := by decide
@[simp] theorem wy_yNd_ne_yNo : yNd ≠ yNo := by decide
@[simp] theorem wy_yNd_ne_yB : yNd ≠ yB := by decide
@[simp] theorem wy_yNd_ne_yX : yNd ≠ yX := by decide
@[simp] theorem wy_yNd_ne_yAp : yNd ≠ yAp := by decide
@[simp] theorem wy_yNd_ne_yS2 : yNd ≠ yS2 := by decide
@[simp] theorem wy_yNd_ne_yVa2 : yNd ≠ yVa2 := by decide
@[simp] theorem wy_yNd_ne_yK : yNd ≠ yK := by decide
@[simp] theorem wy_yNd_ne_yO : yNd ≠ yO := by decide
@[simp] theorem wy_yNd_ne_yE3 : yNd ≠ yE3 := by decide
@[simp] theorem wy_yNd_ne_lFl : yNd ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yNd : lFl ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lDh : yNd ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yNd : lDh ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lDt : yNd ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yNd : lDt ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lDg : yNd ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yNd : lDg ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lDi : yNd ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yNd : lDi ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lRp : yNd ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yNd : lRp ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lRn : yNd ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yNd : lRn ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_kFu : yNd ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yNd : kFu ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_kD : yNd ≠ kD := by decide
@[simp] theorem wy_kD_ne_yNd : kD ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lFle : yNd ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yNd : lFle ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lDir : yNd ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yNd : lDir ≠ yNd := by decide
@[simp] theorem wy_yNd_ne_lKb : yNd ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yNd : lKb ≠ yNd := by decide
@[simp] theorem wy_yI_ne_yV : yI ≠ yV := by decide
@[simp] theorem wy_yI_ne_yHd : yI ≠ yHd := by decide
@[simp] theorem wy_yI_ne_yVa : yI ≠ yVa := by decide
@[simp] theorem wy_yI_ne_ySm : yI ≠ ySm := by decide
@[simp] theorem wy_yI_ne_yAr : yI ≠ yAr := by decide
@[simp] theorem wy_yI_ne_yNd : yI ≠ yNd := by decide
@[simp] theorem wy_yI_ne_yN : yI ≠ yN := by decide
@[simp] theorem wy_yI_ne_yA : yI ≠ yA := by decide
@[simp] theorem wy_yI_ne_yNo : yI ≠ yNo := by decide
@[simp] theorem wy_yI_ne_yB : yI ≠ yB := by decide
@[simp] theorem wy_yI_ne_yX : yI ≠ yX := by decide
@[simp] theorem wy_yI_ne_yAp : yI ≠ yAp := by decide
@[simp] theorem wy_yI_ne_yS2 : yI ≠ yS2 := by decide
@[simp] theorem wy_yI_ne_yVa2 : yI ≠ yVa2 := by decide
@[simp] theorem wy_yI_ne_yK : yI ≠ yK := by decide
@[simp] theorem wy_yI_ne_yO : yI ≠ yO := by decide
@[simp] theorem wy_yI_ne_yE3 : yI ≠ yE3 := by decide
@[simp] theorem wy_yI_ne_lFl : yI ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yI : lFl ≠ yI := by decide
@[simp] theorem wy_yI_ne_lDh : yI ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yI : lDh ≠ yI := by decide
@[simp] theorem wy_yI_ne_lDt : yI ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yI : lDt ≠ yI := by decide
@[simp] theorem wy_yI_ne_lDg : yI ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yI : lDg ≠ yI := by decide
@[simp] theorem wy_yI_ne_lDi : yI ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yI : lDi ≠ yI := by decide
@[simp] theorem wy_yI_ne_lRp : yI ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yI : lRp ≠ yI := by decide
@[simp] theorem wy_yI_ne_lRn : yI ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yI : lRn ≠ yI := by decide
@[simp] theorem wy_yI_ne_kFu : yI ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yI : kFu ≠ yI := by decide
@[simp] theorem wy_yI_ne_kD : yI ≠ kD := by decide
@[simp] theorem wy_kD_ne_yI : kD ≠ yI := by decide
@[simp] theorem wy_yI_ne_lFle : yI ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yI : lFle ≠ yI := by decide
@[simp] theorem wy_yI_ne_lDir : yI ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yI : lDir ≠ yI := by decide
@[simp] theorem wy_yI_ne_lKb : yI ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yI : lKb ≠ yI := by decide
@[simp] theorem wy_yN_ne_yV : yN ≠ yV := by decide
@[simp] theorem wy_yN_ne_yHd : yN ≠ yHd := by decide
@[simp] theorem wy_yN_ne_yVa : yN ≠ yVa := by decide
@[simp] theorem wy_yN_ne_ySm : yN ≠ ySm := by decide
@[simp] theorem wy_yN_ne_yAr : yN ≠ yAr := by decide
@[simp] theorem wy_yN_ne_yNd : yN ≠ yNd := by decide
@[simp] theorem wy_yN_ne_yI : yN ≠ yI := by decide
@[simp] theorem wy_yN_ne_yA : yN ≠ yA := by decide
@[simp] theorem wy_yN_ne_yNo : yN ≠ yNo := by decide
@[simp] theorem wy_yN_ne_yB : yN ≠ yB := by decide
@[simp] theorem wy_yN_ne_yX : yN ≠ yX := by decide
@[simp] theorem wy_yN_ne_yAp : yN ≠ yAp := by decide
@[simp] theorem wy_yN_ne_yS2 : yN ≠ yS2 := by decide
@[simp] theorem wy_yN_ne_yVa2 : yN ≠ yVa2 := by decide
@[simp] theorem wy_yN_ne_yK : yN ≠ yK := by decide
@[simp] theorem wy_yN_ne_yO : yN ≠ yO := by decide
@[simp] theorem wy_yN_ne_yE3 : yN ≠ yE3 := by decide
@[simp] theorem wy_yN_ne_lFl : yN ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yN : lFl ≠ yN := by decide
@[simp] theorem wy_yN_ne_lDh : yN ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yN : lDh ≠ yN := by decide
@[simp] theorem wy_yN_ne_lDt : yN ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yN : lDt ≠ yN := by decide
@[simp] theorem wy_yN_ne_lDg : yN ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yN : lDg ≠ yN := by decide
@[simp] theorem wy_yN_ne_lDi : yN ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yN : lDi ≠ yN := by decide
@[simp] theorem wy_yN_ne_lRp : yN ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yN : lRp ≠ yN := by decide
@[simp] theorem wy_yN_ne_lRn : yN ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yN : lRn ≠ yN := by decide
@[simp] theorem wy_yN_ne_kFu : yN ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yN : kFu ≠ yN := by decide
@[simp] theorem wy_yN_ne_kD : yN ≠ kD := by decide
@[simp] theorem wy_kD_ne_yN : kD ≠ yN := by decide
@[simp] theorem wy_yN_ne_lFle : yN ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yN : lFle ≠ yN := by decide
@[simp] theorem wy_yN_ne_lDir : yN ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yN : lDir ≠ yN := by decide
@[simp] theorem wy_yN_ne_lKb : yN ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yN : lKb ≠ yN := by decide
@[simp] theorem wy_yA_ne_yV : yA ≠ yV := by decide
@[simp] theorem wy_yA_ne_yHd : yA ≠ yHd := by decide
@[simp] theorem wy_yA_ne_yVa : yA ≠ yVa := by decide
@[simp] theorem wy_yA_ne_ySm : yA ≠ ySm := by decide
@[simp] theorem wy_yA_ne_yAr : yA ≠ yAr := by decide
@[simp] theorem wy_yA_ne_yNd : yA ≠ yNd := by decide
@[simp] theorem wy_yA_ne_yI : yA ≠ yI := by decide
@[simp] theorem wy_yA_ne_yN : yA ≠ yN := by decide
@[simp] theorem wy_yA_ne_yNo : yA ≠ yNo := by decide
@[simp] theorem wy_yA_ne_yB : yA ≠ yB := by decide
@[simp] theorem wy_yA_ne_yX : yA ≠ yX := by decide
@[simp] theorem wy_yA_ne_yAp : yA ≠ yAp := by decide
@[simp] theorem wy_yA_ne_yS2 : yA ≠ yS2 := by decide
@[simp] theorem wy_yA_ne_yVa2 : yA ≠ yVa2 := by decide
@[simp] theorem wy_yA_ne_yK : yA ≠ yK := by decide
@[simp] theorem wy_yA_ne_yO : yA ≠ yO := by decide
@[simp] theorem wy_yA_ne_yE3 : yA ≠ yE3 := by decide
@[simp] theorem wy_yA_ne_lFl : yA ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yA : lFl ≠ yA := by decide
@[simp] theorem wy_yA_ne_lDh : yA ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yA : lDh ≠ yA := by decide
@[simp] theorem wy_yA_ne_lDt : yA ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yA : lDt ≠ yA := by decide
@[simp] theorem wy_yA_ne_lDg : yA ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yA : lDg ≠ yA := by decide
@[simp] theorem wy_yA_ne_lDi : yA ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yA : lDi ≠ yA := by decide
@[simp] theorem wy_yA_ne_lRp : yA ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yA : lRp ≠ yA := by decide
@[simp] theorem wy_yA_ne_lRn : yA ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yA : lRn ≠ yA := by decide
@[simp] theorem wy_yA_ne_kFu : yA ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yA : kFu ≠ yA := by decide
@[simp] theorem wy_yA_ne_kD : yA ≠ kD := by decide
@[simp] theorem wy_kD_ne_yA : kD ≠ yA := by decide
@[simp] theorem wy_yA_ne_lFle : yA ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yA : lFle ≠ yA := by decide
@[simp] theorem wy_yA_ne_lDir : yA ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yA : lDir ≠ yA := by decide
@[simp] theorem wy_yA_ne_lKb : yA ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yA : lKb ≠ yA := by decide
@[simp] theorem wy_yNo_ne_yV : yNo ≠ yV := by decide
@[simp] theorem wy_yNo_ne_yHd : yNo ≠ yHd := by decide
@[simp] theorem wy_yNo_ne_yVa : yNo ≠ yVa := by decide
@[simp] theorem wy_yNo_ne_ySm : yNo ≠ ySm := by decide
@[simp] theorem wy_yNo_ne_yAr : yNo ≠ yAr := by decide
@[simp] theorem wy_yNo_ne_yNd : yNo ≠ yNd := by decide
@[simp] theorem wy_yNo_ne_yI : yNo ≠ yI := by decide
@[simp] theorem wy_yNo_ne_yN : yNo ≠ yN := by decide
@[simp] theorem wy_yNo_ne_yA : yNo ≠ yA := by decide
@[simp] theorem wy_yNo_ne_yB : yNo ≠ yB := by decide
@[simp] theorem wy_yNo_ne_yX : yNo ≠ yX := by decide
@[simp] theorem wy_yNo_ne_yAp : yNo ≠ yAp := by decide
@[simp] theorem wy_yNo_ne_yS2 : yNo ≠ yS2 := by decide
@[simp] theorem wy_yNo_ne_yVa2 : yNo ≠ yVa2 := by decide
@[simp] theorem wy_yNo_ne_yK : yNo ≠ yK := by decide
@[simp] theorem wy_yNo_ne_yO : yNo ≠ yO := by decide
@[simp] theorem wy_yNo_ne_yE3 : yNo ≠ yE3 := by decide
@[simp] theorem wy_yNo_ne_lFl : yNo ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yNo : lFl ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lDh : yNo ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yNo : lDh ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lDt : yNo ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yNo : lDt ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lDg : yNo ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yNo : lDg ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lDi : yNo ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yNo : lDi ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lRp : yNo ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yNo : lRp ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lRn : yNo ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yNo : lRn ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_kFu : yNo ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yNo : kFu ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_kD : yNo ≠ kD := by decide
@[simp] theorem wy_kD_ne_yNo : kD ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lFle : yNo ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yNo : lFle ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lDir : yNo ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yNo : lDir ≠ yNo := by decide
@[simp] theorem wy_yNo_ne_lKb : yNo ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yNo : lKb ≠ yNo := by decide
@[simp] theorem wy_yB_ne_yV : yB ≠ yV := by decide
@[simp] theorem wy_yB_ne_yHd : yB ≠ yHd := by decide
@[simp] theorem wy_yB_ne_yVa : yB ≠ yVa := by decide
@[simp] theorem wy_yB_ne_ySm : yB ≠ ySm := by decide
@[simp] theorem wy_yB_ne_yAr : yB ≠ yAr := by decide
@[simp] theorem wy_yB_ne_yNd : yB ≠ yNd := by decide
@[simp] theorem wy_yB_ne_yI : yB ≠ yI := by decide
@[simp] theorem wy_yB_ne_yN : yB ≠ yN := by decide
@[simp] theorem wy_yB_ne_yA : yB ≠ yA := by decide
@[simp] theorem wy_yB_ne_yNo : yB ≠ yNo := by decide
@[simp] theorem wy_yB_ne_yX : yB ≠ yX := by decide
@[simp] theorem wy_yB_ne_yAp : yB ≠ yAp := by decide
@[simp] theorem wy_yB_ne_yS2 : yB ≠ yS2 := by decide
@[simp] theorem wy_yB_ne_yVa2 : yB ≠ yVa2 := by decide
@[simp] theorem wy_yB_ne_yK : yB ≠ yK := by decide
@[simp] theorem wy_yB_ne_yO : yB ≠ yO := by decide
@[simp] theorem wy_yB_ne_yE3 : yB ≠ yE3 := by decide
@[simp] theorem wy_yB_ne_lFl : yB ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yB : lFl ≠ yB := by decide
@[simp] theorem wy_yB_ne_lDh : yB ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yB : lDh ≠ yB := by decide
@[simp] theorem wy_yB_ne_lDt : yB ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yB : lDt ≠ yB := by decide
@[simp] theorem wy_yB_ne_lDg : yB ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yB : lDg ≠ yB := by decide
@[simp] theorem wy_yB_ne_lDi : yB ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yB : lDi ≠ yB := by decide
@[simp] theorem wy_yB_ne_lRp : yB ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yB : lRp ≠ yB := by decide
@[simp] theorem wy_yB_ne_lRn : yB ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yB : lRn ≠ yB := by decide
@[simp] theorem wy_yB_ne_kFu : yB ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yB : kFu ≠ yB := by decide
@[simp] theorem wy_yB_ne_kD : yB ≠ kD := by decide
@[simp] theorem wy_kD_ne_yB : kD ≠ yB := by decide
@[simp] theorem wy_yB_ne_lFle : yB ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yB : lFle ≠ yB := by decide
@[simp] theorem wy_yB_ne_lDir : yB ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yB : lDir ≠ yB := by decide
@[simp] theorem wy_yB_ne_lKb : yB ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yB : lKb ≠ yB := by decide
@[simp] theorem wy_yX_ne_yV : yX ≠ yV := by decide
@[simp] theorem wy_yX_ne_yHd : yX ≠ yHd := by decide
@[simp] theorem wy_yX_ne_yVa : yX ≠ yVa := by decide
@[simp] theorem wy_yX_ne_ySm : yX ≠ ySm := by decide
@[simp] theorem wy_yX_ne_yAr : yX ≠ yAr := by decide
@[simp] theorem wy_yX_ne_yNd : yX ≠ yNd := by decide
@[simp] theorem wy_yX_ne_yI : yX ≠ yI := by decide
@[simp] theorem wy_yX_ne_yN : yX ≠ yN := by decide
@[simp] theorem wy_yX_ne_yA : yX ≠ yA := by decide
@[simp] theorem wy_yX_ne_yNo : yX ≠ yNo := by decide
@[simp] theorem wy_yX_ne_yB : yX ≠ yB := by decide
@[simp] theorem wy_yX_ne_yAp : yX ≠ yAp := by decide
@[simp] theorem wy_yX_ne_yS2 : yX ≠ yS2 := by decide
@[simp] theorem wy_yX_ne_yVa2 : yX ≠ yVa2 := by decide
@[simp] theorem wy_yX_ne_yK : yX ≠ yK := by decide
@[simp] theorem wy_yX_ne_yO : yX ≠ yO := by decide
@[simp] theorem wy_yX_ne_yE3 : yX ≠ yE3 := by decide
@[simp] theorem wy_yX_ne_lFl : yX ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yX : lFl ≠ yX := by decide
@[simp] theorem wy_yX_ne_lDh : yX ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yX : lDh ≠ yX := by decide
@[simp] theorem wy_yX_ne_lDt : yX ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yX : lDt ≠ yX := by decide
@[simp] theorem wy_yX_ne_lDg : yX ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yX : lDg ≠ yX := by decide
@[simp] theorem wy_yX_ne_lDi : yX ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yX : lDi ≠ yX := by decide
@[simp] theorem wy_yX_ne_lRp : yX ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yX : lRp ≠ yX := by decide
@[simp] theorem wy_yX_ne_lRn : yX ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yX : lRn ≠ yX := by decide
@[simp] theorem wy_yX_ne_kFu : yX ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yX : kFu ≠ yX := by decide
@[simp] theorem wy_yX_ne_kD : yX ≠ kD := by decide
@[simp] theorem wy_kD_ne_yX : kD ≠ yX := by decide
@[simp] theorem wy_yX_ne_lFle : yX ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yX : lFle ≠ yX := by decide
@[simp] theorem wy_yX_ne_lDir : yX ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yX : lDir ≠ yX := by decide
@[simp] theorem wy_yX_ne_lKb : yX ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yX : lKb ≠ yX := by decide
@[simp] theorem wy_yAp_ne_yV : yAp ≠ yV := by decide
@[simp] theorem wy_yAp_ne_yHd : yAp ≠ yHd := by decide
@[simp] theorem wy_yAp_ne_yVa : yAp ≠ yVa := by decide
@[simp] theorem wy_yAp_ne_ySm : yAp ≠ ySm := by decide
@[simp] theorem wy_yAp_ne_yAr : yAp ≠ yAr := by decide
@[simp] theorem wy_yAp_ne_yNd : yAp ≠ yNd := by decide
@[simp] theorem wy_yAp_ne_yI : yAp ≠ yI := by decide
@[simp] theorem wy_yAp_ne_yN : yAp ≠ yN := by decide
@[simp] theorem wy_yAp_ne_yA : yAp ≠ yA := by decide
@[simp] theorem wy_yAp_ne_yNo : yAp ≠ yNo := by decide
@[simp] theorem wy_yAp_ne_yB : yAp ≠ yB := by decide
@[simp] theorem wy_yAp_ne_yX : yAp ≠ yX := by decide
@[simp] theorem wy_yAp_ne_yS2 : yAp ≠ yS2 := by decide
@[simp] theorem wy_yAp_ne_yVa2 : yAp ≠ yVa2 := by decide
@[simp] theorem wy_yAp_ne_yK : yAp ≠ yK := by decide
@[simp] theorem wy_yAp_ne_yO : yAp ≠ yO := by decide
@[simp] theorem wy_yAp_ne_yE3 : yAp ≠ yE3 := by decide
@[simp] theorem wy_yAp_ne_lFl : yAp ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yAp : lFl ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lDh : yAp ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yAp : lDh ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lDt : yAp ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yAp : lDt ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lDg : yAp ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yAp : lDg ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lDi : yAp ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yAp : lDi ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lRp : yAp ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yAp : lRp ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lRn : yAp ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yAp : lRn ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_kFu : yAp ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yAp : kFu ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_kD : yAp ≠ kD := by decide
@[simp] theorem wy_kD_ne_yAp : kD ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lFle : yAp ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yAp : lFle ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lDir : yAp ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yAp : lDir ≠ yAp := by decide
@[simp] theorem wy_yAp_ne_lKb : yAp ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yAp : lKb ≠ yAp := by decide
@[simp] theorem wy_yS2_ne_yV : yS2 ≠ yV := by decide
@[simp] theorem wy_yS2_ne_yHd : yS2 ≠ yHd := by decide
@[simp] theorem wy_yS2_ne_yVa : yS2 ≠ yVa := by decide
@[simp] theorem wy_yS2_ne_ySm : yS2 ≠ ySm := by decide
@[simp] theorem wy_yS2_ne_yAr : yS2 ≠ yAr := by decide
@[simp] theorem wy_yS2_ne_yNd : yS2 ≠ yNd := by decide
@[simp] theorem wy_yS2_ne_yI : yS2 ≠ yI := by decide
@[simp] theorem wy_yS2_ne_yN : yS2 ≠ yN := by decide
@[simp] theorem wy_yS2_ne_yA : yS2 ≠ yA := by decide
@[simp] theorem wy_yS2_ne_yNo : yS2 ≠ yNo := by decide
@[simp] theorem wy_yS2_ne_yB : yS2 ≠ yB := by decide
@[simp] theorem wy_yS2_ne_yX : yS2 ≠ yX := by decide
@[simp] theorem wy_yS2_ne_yAp : yS2 ≠ yAp := by decide
@[simp] theorem wy_yS2_ne_yVa2 : yS2 ≠ yVa2 := by decide
@[simp] theorem wy_yS2_ne_yK : yS2 ≠ yK := by decide
@[simp] theorem wy_yS2_ne_yO : yS2 ≠ yO := by decide
@[simp] theorem wy_yS2_ne_yE3 : yS2 ≠ yE3 := by decide
@[simp] theorem wy_yS2_ne_lFl : yS2 ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yS2 : lFl ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lDh : yS2 ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yS2 : lDh ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lDt : yS2 ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yS2 : lDt ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lDg : yS2 ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yS2 : lDg ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lDi : yS2 ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yS2 : lDi ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lRp : yS2 ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yS2 : lRp ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lRn : yS2 ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yS2 : lRn ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_kFu : yS2 ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yS2 : kFu ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_kD : yS2 ≠ kD := by decide
@[simp] theorem wy_kD_ne_yS2 : kD ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lFle : yS2 ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yS2 : lFle ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lDir : yS2 ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yS2 : lDir ≠ yS2 := by decide
@[simp] theorem wy_yS2_ne_lKb : yS2 ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yS2 : lKb ≠ yS2 := by decide
@[simp] theorem wy_yVa2_ne_yV : yVa2 ≠ yV := by decide
@[simp] theorem wy_yVa2_ne_yHd : yVa2 ≠ yHd := by decide
@[simp] theorem wy_yVa2_ne_yVa : yVa2 ≠ yVa := by decide
@[simp] theorem wy_yVa2_ne_ySm : yVa2 ≠ ySm := by decide
@[simp] theorem wy_yVa2_ne_yAr : yVa2 ≠ yAr := by decide
@[simp] theorem wy_yVa2_ne_yNd : yVa2 ≠ yNd := by decide
@[simp] theorem wy_yVa2_ne_yI : yVa2 ≠ yI := by decide
@[simp] theorem wy_yVa2_ne_yN : yVa2 ≠ yN := by decide
@[simp] theorem wy_yVa2_ne_yA : yVa2 ≠ yA := by decide
@[simp] theorem wy_yVa2_ne_yNo : yVa2 ≠ yNo := by decide
@[simp] theorem wy_yVa2_ne_yB : yVa2 ≠ yB := by decide
@[simp] theorem wy_yVa2_ne_yX : yVa2 ≠ yX := by decide
@[simp] theorem wy_yVa2_ne_yAp : yVa2 ≠ yAp := by decide
@[simp] theorem wy_yVa2_ne_yS2 : yVa2 ≠ yS2 := by decide
@[simp] theorem wy_yVa2_ne_yK : yVa2 ≠ yK := by decide
@[simp] theorem wy_yVa2_ne_yO : yVa2 ≠ yO := by decide
@[simp] theorem wy_yVa2_ne_yE3 : yVa2 ≠ yE3 := by decide
@[simp] theorem wy_yVa2_ne_lFl : yVa2 ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yVa2 : lFl ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lDh : yVa2 ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yVa2 : lDh ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lDt : yVa2 ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yVa2 : lDt ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lDg : yVa2 ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yVa2 : lDg ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lDi : yVa2 ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yVa2 : lDi ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lRp : yVa2 ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yVa2 : lRp ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lRn : yVa2 ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yVa2 : lRn ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_kFu : yVa2 ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yVa2 : kFu ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_kD : yVa2 ≠ kD := by decide
@[simp] theorem wy_kD_ne_yVa2 : kD ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lFle : yVa2 ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yVa2 : lFle ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lDir : yVa2 ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yVa2 : lDir ≠ yVa2 := by decide
@[simp] theorem wy_yVa2_ne_lKb : yVa2 ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yVa2 : lKb ≠ yVa2 := by decide
@[simp] theorem wy_yK_ne_yV : yK ≠ yV := by decide
@[simp] theorem wy_yK_ne_yHd : yK ≠ yHd := by decide
@[simp] theorem wy_yK_ne_yVa : yK ≠ yVa := by decide
@[simp] theorem wy_yK_ne_ySm : yK ≠ ySm := by decide
@[simp] theorem wy_yK_ne_yAr : yK ≠ yAr := by decide
@[simp] theorem wy_yK_ne_yNd : yK ≠ yNd := by decide
@[simp] theorem wy_yK_ne_yI : yK ≠ yI := by decide
@[simp] theorem wy_yK_ne_yN : yK ≠ yN := by decide
@[simp] theorem wy_yK_ne_yA : yK ≠ yA := by decide
@[simp] theorem wy_yK_ne_yNo : yK ≠ yNo := by decide
@[simp] theorem wy_yK_ne_yB : yK ≠ yB := by decide
@[simp] theorem wy_yK_ne_yX : yK ≠ yX := by decide
@[simp] theorem wy_yK_ne_yAp : yK ≠ yAp := by decide
@[simp] theorem wy_yK_ne_yS2 : yK ≠ yS2 := by decide
@[simp] theorem wy_yK_ne_yVa2 : yK ≠ yVa2 := by decide
@[simp] theorem wy_yK_ne_yO : yK ≠ yO := by decide
@[simp] theorem wy_yK_ne_yE3 : yK ≠ yE3 := by decide
@[simp] theorem wy_yK_ne_lFl : yK ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yK : lFl ≠ yK := by decide
@[simp] theorem wy_yK_ne_lDh : yK ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yK : lDh ≠ yK := by decide
@[simp] theorem wy_yK_ne_lDt : yK ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yK : lDt ≠ yK := by decide
@[simp] theorem wy_yK_ne_lDg : yK ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yK : lDg ≠ yK := by decide
@[simp] theorem wy_yK_ne_lDi : yK ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yK : lDi ≠ yK := by decide
@[simp] theorem wy_yK_ne_lRp : yK ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yK : lRp ≠ yK := by decide
@[simp] theorem wy_yK_ne_lRn : yK ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yK : lRn ≠ yK := by decide
@[simp] theorem wy_yK_ne_kFu : yK ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yK : kFu ≠ yK := by decide
@[simp] theorem wy_yK_ne_kD : yK ≠ kD := by decide
@[simp] theorem wy_kD_ne_yK : kD ≠ yK := by decide
@[simp] theorem wy_yK_ne_lFle : yK ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yK : lFle ≠ yK := by decide
@[simp] theorem wy_yK_ne_lDir : yK ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yK : lDir ≠ yK := by decide
@[simp] theorem wy_yK_ne_lKb : yK ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yK : lKb ≠ yK := by decide
@[simp] theorem wy_yO_ne_yV : yO ≠ yV := by decide
@[simp] theorem wy_yO_ne_yHd : yO ≠ yHd := by decide
@[simp] theorem wy_yO_ne_yVa : yO ≠ yVa := by decide
@[simp] theorem wy_yO_ne_ySm : yO ≠ ySm := by decide
@[simp] theorem wy_yO_ne_yAr : yO ≠ yAr := by decide
@[simp] theorem wy_yO_ne_yNd : yO ≠ yNd := by decide
@[simp] theorem wy_yO_ne_yI : yO ≠ yI := by decide
@[simp] theorem wy_yO_ne_yN : yO ≠ yN := by decide
@[simp] theorem wy_yO_ne_yA : yO ≠ yA := by decide
@[simp] theorem wy_yO_ne_yNo : yO ≠ yNo := by decide
@[simp] theorem wy_yO_ne_yB : yO ≠ yB := by decide
@[simp] theorem wy_yO_ne_yX : yO ≠ yX := by decide
@[simp] theorem wy_yO_ne_yAp : yO ≠ yAp := by decide
@[simp] theorem wy_yO_ne_yS2 : yO ≠ yS2 := by decide
@[simp] theorem wy_yO_ne_yVa2 : yO ≠ yVa2 := by decide
@[simp] theorem wy_yO_ne_yK : yO ≠ yK := by decide
@[simp] theorem wy_yO_ne_yE3 : yO ≠ yE3 := by decide
@[simp] theorem wy_yO_ne_lFl : yO ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yO : lFl ≠ yO := by decide
@[simp] theorem wy_yO_ne_lDh : yO ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yO : lDh ≠ yO := by decide
@[simp] theorem wy_yO_ne_lDt : yO ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yO : lDt ≠ yO := by decide
@[simp] theorem wy_yO_ne_lDg : yO ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yO : lDg ≠ yO := by decide
@[simp] theorem wy_yO_ne_lDi : yO ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yO : lDi ≠ yO := by decide
@[simp] theorem wy_yO_ne_lRp : yO ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yO : lRp ≠ yO := by decide
@[simp] theorem wy_yO_ne_lRn : yO ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yO : lRn ≠ yO := by decide
@[simp] theorem wy_yO_ne_kFu : yO ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yO : kFu ≠ yO := by decide
@[simp] theorem wy_yO_ne_kD : yO ≠ kD := by decide
@[simp] theorem wy_kD_ne_yO : kD ≠ yO := by decide
@[simp] theorem wy_yO_ne_lFle : yO ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yO : lFle ≠ yO := by decide
@[simp] theorem wy_yO_ne_lDir : yO ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yO : lDir ≠ yO := by decide
@[simp] theorem wy_yO_ne_lKb : yO ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yO : lKb ≠ yO := by decide
@[simp] theorem wy_yE3_ne_yV : yE3 ≠ yV := by decide
@[simp] theorem wy_yE3_ne_yHd : yE3 ≠ yHd := by decide
@[simp] theorem wy_yE3_ne_yVa : yE3 ≠ yVa := by decide
@[simp] theorem wy_yE3_ne_ySm : yE3 ≠ ySm := by decide
@[simp] theorem wy_yE3_ne_yAr : yE3 ≠ yAr := by decide
@[simp] theorem wy_yE3_ne_yNd : yE3 ≠ yNd := by decide
@[simp] theorem wy_yE3_ne_yI : yE3 ≠ yI := by decide
@[simp] theorem wy_yE3_ne_yN : yE3 ≠ yN := by decide
@[simp] theorem wy_yE3_ne_yA : yE3 ≠ yA := by decide
@[simp] theorem wy_yE3_ne_yNo : yE3 ≠ yNo := by decide
@[simp] theorem wy_yE3_ne_yB : yE3 ≠ yB := by decide
@[simp] theorem wy_yE3_ne_yX : yE3 ≠ yX := by decide
@[simp] theorem wy_yE3_ne_yAp : yE3 ≠ yAp := by decide
@[simp] theorem wy_yE3_ne_yS2 : yE3 ≠ yS2 := by decide
@[simp] theorem wy_yE3_ne_yVa2 : yE3 ≠ yVa2 := by decide
@[simp] theorem wy_yE3_ne_yK : yE3 ≠ yK := by decide
@[simp] theorem wy_yE3_ne_yO : yE3 ≠ yO := by decide
@[simp] theorem wy_yE3_ne_lFl : yE3 ≠ lFl := by decide
@[simp] theorem wy_lFl_ne_yE3 : lFl ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lDh : yE3 ≠ lDh := by decide
@[simp] theorem wy_lDh_ne_yE3 : lDh ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lDt : yE3 ≠ lDt := by decide
@[simp] theorem wy_lDt_ne_yE3 : lDt ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lDg : yE3 ≠ lDg := by decide
@[simp] theorem wy_lDg_ne_yE3 : lDg ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lDi : yE3 ≠ lDi := by decide
@[simp] theorem wy_lDi_ne_yE3 : lDi ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lRp : yE3 ≠ lRp := by decide
@[simp] theorem wy_lRp_ne_yE3 : lRp ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lRn : yE3 ≠ lRn := by decide
@[simp] theorem wy_lRn_ne_yE3 : lRn ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_kFu : yE3 ≠ kFu := by decide
@[simp] theorem wy_kFu_ne_yE3 : kFu ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_kD : yE3 ≠ kD := by decide
@[simp] theorem wy_kD_ne_yE3 : kD ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lFle : yE3 ≠ lFle := by decide
@[simp] theorem wy_lFle_ne_yE3 : lFle ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lDir : yE3 ≠ lDir := by decide
@[simp] theorem wy_lDir_ne_yE3 : lDir ≠ yE3 := by decide
@[simp] theorem wy_yE3_ne_lKb : yE3 ≠ lKb := by decide
@[simp] theorem wy_lKb_ne_yE3 : lKb ≠ yE3 := by decide

def wapParams : List MlS := [kFu, kD, yV, yHd, yVa, ySm, yAr, yNd, yI, yN]
def wapLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, yA, yNo, yB, yX, yAp, yS2, yVa2, yK, yO, yE3,
  ExPre.aX]

def wapRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local yS2 (.cmp .equal (vv yAp) (vv yNo))) (.seq (.call (some (some (.local, yVa2), none)) ExPre.fAppend [vv yVa, vv yA]) (.seq (.assign .local yK (.load .one (vv yVa2))) (.seq (.call (some (some (.local, yO), none)) fWai [vv kFu, vv kD, vv yHd, vv yVa2, vv yK]) (.ite (.cmp .equal (vv yO) (.const 0)) (.seq (.call (some (some (.local, yX), none)) fWap [vv kFu, vv kD, vv yAp, vv yHd, vv yVa2, vv yS2, vv yAr, vv yNd, .op .add [vv yI, .const 1], vv yN]) (.return (vv yX))) (.seq (.call (some (some (.local, yE3), none)) ExK.fMka [.op .sub [vv yO, .const 1], vv yAr, .op .add [vv yI, .const 1], vv yN]) (.return (.op .add [.shift .lsl (vv yE3) (.const 1), .const 1])))))))

def wapCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv yI) (vv yN)) (.seq (.assign .local yA (.load .one (.op .add [vv yAr, .op .add [.panop .mul [vv yI, .const 8], .const 8]]))) (.seq (.assign .local yNo (.load .one (.op .add [vv yNd, .op .add [.panop .mul [vv yI, .const 8], .const 8]]))) (.ite (tagIsE yV 5) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv yV)) (.seq eViewP (.seq (.assign .local yB (.load .one (.op .add [vv lRp, .const 8]))) (.seq (.call (some (some (.local, yX), none)) fBp [vv yB, vv yI, vv yAr, .op .add [vv yI, .const 1], vv yN]) (.return (vv yX))))))) (.ite (vv ySm) (.seq (.assign .local yAp (vv yNo)) (wapRest C)) (.seq (.call (some (some (.local, yAp), none)) fInternApp [vv yV, vv yA]) (wapRest C)))))) (.return (.shift .lsl (vv yV) (.const 1)))

def wapBody (C : Ctx) : ProgHOL 64 := prologue wapLocals (wapCore C)


section
variable {σ : Type}

theorem wap_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wapLocals → (ctxEnv C ++ wapParams.zip vals).get x = none :=
  Knot.params_none C wapLocals wapParams vals (by decide) (by decide)

theorem cellA_idx (C : Ctx) (o i : Nat) : cellA C o + (BitVec.ofNat 64 i * 8#64 + 8#64) = cellA C (o + 1 + i) := by
  rw [show BitVec.ofNat 64 i * 8#64 + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) from Big.add8_eq i]
  unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem wap_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hcwap : C.code.lookup fWap = some (wapParams.map (fun p => (p, ShapeHOL.one)), wapBody C, .one))
    (hcbp : C.code.lookup fBp = some (bpParams.map (fun p => (p, ShapeHOL.one)), bpBody, .one))
    (hcwai : C.code.lookup fWai = some (waiParams.map (fun p => (p, ShapeHOL.one)), waiBody C, .one))
    (hcapp : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)),
      ExPre.appBody C, .one))
    (hcm : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
      ExK.mkaBody, .one))
    (hcI : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (d : Nat) (args nodes : Array EIdx) (oa on : Nat) (hba : BlkAt C.H oa (args.toList.map Enc.idxW))
    (hbn : BlkAt C.H on (nodes.toList.map Enc.idxW)) (hnd : nodes.size = args.size) (hsz : args.size < 2 ^ 58)
    (hBp : ∀ (H : List (BitVec 64)) s1 t st, C.H <+: H → st < 2 ^ 63 → ∀ i, i ≤ args.size →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (bpParams.zip [Enc.idxW t, BitVec.ofNat 64 st, cellA C oa, BitVec.ofNat 64 i,
        BitVec.ofNat 64 args.size])) bpBody s1 (betaPeel t st args i) (PostWS (ctxH C H)))
    (hWai : ∀ (H : List (BitVec 64)) s1 hd (va : Array EIdx) ov, C.H <+: H → BlkAt H ov (va.toList.map Enc.idxW) →
      va.size < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (waiParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
        Enc.idxW hd, cellA C ov, BitVec.ofNat 64 va.size])) (waiBody C) s1
        (whnfAppIota mode (knot mode C n) C.fe d hd va va.size) (UD.PostO (ctxH C H))) :
    ∀ k (H : List (BitVec 64)) s v hd (va : Array EIdx) ov same i, C.H <+: H →
      BlkAt H ov (va.toList.map Enc.idxW) → va.size < 2 ^ 58 → args.size - i = k → i ≤ args.size →
      SpecR (σ := σ) (Pre (ctxH C H) s (wapParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW v, Enc.idxW hd,
        cellA C ov, boolW same, cellA C oa, cellA C on, BitVec.ofNat 64 i, BitVec.ofNat 64 args.size])) (wapBody C) s
        (whnfApp mode (knot mode C n) C.fe d v hd va same args nodes i) (PostWS (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro H s v hd va ov same i hpre hbv hvs hk hi
    refine specR_prologue (postWS_locals _) (wap_none _ _) ?_
    unfold wapCore
    rw [whnfApp, dite_eq_right (by omega)]
    have hlw := word_lt_iff i args.size (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, wapParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr (by omega)]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ (encWS (.done v)) (by simp +decide [sev, Env.get, wapParams, ctxEnv, encWS])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro H s v hd va ov same i hpre hbv hvs hk hi
    have hlt : i < args.size := by omega
    have hok' := ctxOK_H hok H
    refine specR_prologue (postWS_locals _) (wap_none _ _) ?_
    unfold wapCore
    rw [whnfApp, dite_eq_left hlt]
    have hlw := word_lt_iff i args.size (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, wapParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      hlw.mpr hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hai : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW args[i]) := by
      have := (blkAt_mono hba hpre).2 i (by simp; omega); simp at this; exact this
    have hni : (ctxH C H).H[on + 1 + i]? = some (Enc.idxW nodes[i]!) := by
      have := (blkAt_mono hbn hpre).2 i (by simp; omega)
      rw [getElem!_pos nodes i (by omega)]; simp at this; exact this
    refine UD.specR_heapLoadI' (C := ctxH C H) yA _ (oa + 1 + i) _ hai (by decide)
      (by simp +decide [sev, Env.get, wapParams, ctxEnv]; exact cellA_idx C oa i) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) yNo _ (on + 1 + i) _ hni (by decide)
      (by simp +decide [sev, Env.get, wapParams, ctxEnv]; exact cellA_idx C on i) ?_
    -- the shared tail, from the applied node `ap`
    have hrest : ∀ (ap : EIdx) (s1 : AState) (Γ : Env), Γ.get yAp = some (Enc.idxW ap) →
        Γ.get yNo = some (Enc.idxW nodes[i]!) → Γ.get yA = some (Enc.idxW args[i]) →
        Γ.get yVa = some (cellA C ov) → Γ.get kFu = some (BitVec.ofNat 64 n) →
        Γ.get kD = some (BitVec.ofNat 64 d) → Γ.get yHd = some (Enc.idxW hd) →
        Γ.get yAr = some (cellA C oa) → Γ.get yNd = some (cellA C on) → Γ.get yI = some (BitVec.ofNat 64 i) →
        Γ.get yN = some (BitVec.ofNat 64 args.size) →
        SpecR (σ := σ) (Inv (ctxH C H) s1 Γ [] (ctxLocals ++ wapLocals)) (wapRest C) s1
          (whnfAppIota mode (knot mode C n) C.fe d hd (va.push args[i]) (va.push args[i]).size >>= fun o =>
            match o with
            | none => whnfApp mode (knot mode C n) C.fe d ap hd (va.push args[i]) (ap == nodes[i]!) args nodes (i + 1)
            | some e2 => mkAppNFrom e2 args (i + 1) >>= fun e3 => pure (WhnfStep.cont e3)) (PostWS (ctxH C H)) := by
      intro ap s1 Γ hAp hNo hA hVa hFu hD hHd hAr hNd hI hN
      unfold wapRest
      have hI1 : ∀ Γ' : Env, Γ'.get yI = some (BitVec.ofNat 64 i) →
          sev Γ' (.op .add [vv yI, .const 1]) = some (BitVec.ofNat 64 (i + 1)) := by
        intro Γ' h'; simp only [sev, sev_vv, h']; simp; exact word_add1_eq i
      have heqb : sev Γ (.cmp .equal (vv yAp) (vv yNo)) = some (boolW (ap == nodes[i]!)) := by
        simp only [sev, sev_vv, hAp, hNo]
        by_cases he : ap = nodes[i]!
        · rw [he]; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        · have : Enc.idxW ap ≠ Enc.idxW nodes[i]! := fun x => he (Enc.idxW_inj x)
          simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, he]
      refine specR_assignI yS2 _ (boolW (ap == nodes[i]!)) (by decide) heqb ?_
      refine ExPre.specR_callApp (C := ctxH C H) hok' hcapp yVa2 (vv yVa) (vv yA) ov _ (Enc.idxW args[i])
        (by decide) hbv (by simp [hVa]; rfl) (by simp [hA]) (fun H2 o2 hp2 hb2 => ?_)
      have hb2' : BlkAt H2 o2 ((va.push args[i]).toList.map Enc.idxW) := by simpa using hb2
      obtain ⟨hlo, hlv⟩ := blkAt_get0 hb2'
      have hw0 : (ctxH C H2).H[o2]? = some (BitVec.ofNat 64 (va.push args[i]).size) := by
        show H2[o2]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
      refine specR_atEntry fun t2 ht2 => ?_
      have hsm := blk_small0 (C := ctxH C H2) (ctxOK_H hok _) ht2.sr hb2'
      simp only [List.length_map, Array.length_toList] at hsm
      refine UD.specR_heapLoadI' (C := ctxH C H2) yK (vv yVa2) o2 _ hw0 (by decide) (by simp; rfl) ?_
      refine specR_callNIH (C := ctxH C H2) yO fWai waiParams [vv kFu, vv kD, vv yHd, vv yVa2, vv yK] (waiBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW hd, cellA C o2, BitVec.ofNat 64 (va.push args[i]).size]
        (by decide) rfl (by decide) hcwai ⟨by simp [hFu], by simp [hD], by simp [hHd], by simp; rfl, by simp, trivial⟩
        (UD.PostO (ctxH C H2)) (fun r w _ _ => w = optW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu waiParams _ rfl hlk)
          (hWai H2 s1 hd (va.push args[i]) o2 (hpre.trans hp2) hb2' (by simp; omega)))
        (fun r w s2 H3 hp3 hw => ?_)
      subst hw
      rcases r with _ | e2
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        refine specR_mono (R := PostWS (ctxH C H3)) ?_ (fun _ h => h) (fun a w s' t ⟨H', hp', hw', hsr'⟩ =>
          ⟨H', (hp2.trans hp3).trans hp', hw', hsr'⟩)
        exact specR_callWS (D := ctxLocals ++ wapLocals) yX fWap wapParams
          [vv kFu, vv kD, vv yAp, vv yHd, vv yVa2, vv yS2, vv yAr, vv yNd, .op .add [vv yI, .const 1], vv yN]
          (wapBody C) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ap, Enc.idxW hd, cellA C o2,
            boolW (ap == nodes[i]!), cellA C oa, cellA C on, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.size]
          (by decide) rfl (by decide) hcwap
          ⟨by simp [hFu], by simp [hD], by simp [hAp], by simp [hHd], by simp; rfl, by simp, by simp [hAr],
            by simp [hNd], hI1 _ (by simp [hI]), by simp [hN], trivial⟩
          (ih H3 s2 ap hd (va.push args[i]) o2 (ap == nodes[i]!) (i + 1) (hpre.trans (hp2.trans hp3))
            (blkAt_mono hb2' hp3) hsm (by omega) (by omega))
      · have hne : optW (some e2) ≠ 0 := WB.idxW_succ_ne e2
        refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine ILP.callE_spec (C := ctxH C H3) yE3 ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
          [.op .sub [vv yO, .const 1], vv yAr, .op .add [vv yI, .const 1], vv yN] ExK.mkaBody
          [Enc.idxW e2, cellA C oa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.toList.length] (by decide) rfl
          (by decide) hcm ⟨by simp [sev, optWG, BitVec.add_sub_cancel], by simp [hAr], hI1 _ (by simp [hI]),
            by simp [hN], trivial⟩
          (ExK.mkAppNFrom_spec ra (ctxH C H3) (ctxOK_H hok _) hcm hcI oa args
            (blkAt_mono hba (hpre.trans (hp2.trans hp3))) (by omega) (i + 1) (by omega) e2 s2) (fun e3 s3 => ?_)
        exact specR_returnI _ (encWS (.cont e3)) (by simp [sev, vv, encWS]) (fun t ht =>
          ⟨H3, hp2.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine Knot.specR_tagIteV yV v 5 (by decide) (by decide) (by simp +decide [Env.get, wapParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [ite_eq_left (show (v.tag == ETag.lam) = true by simp [htg, ETag.lam])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]; rfl) ?_
      refine specR_assignI lDh (vv yV) (Enc.idxW v) (by decide) (by simp +decide [Env.get, wapParams, ctxEnv]) ?_
      refine specR_viewP v (by simp) (by simp +decide [Env.get]; rfl) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun vw P hv htn _ => ?_)
      have h5 : vw.tagN = 5 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, vw = .lam ty b := by
        cases vw <;> simp [ENodeView.tagN] at h5 ⊢
      have hvb : s.store.viewBind v = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      refine specR_loadI' yB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      exact specR_callWS yX fBp bpParams [vv yB, vv yI, vv yAr, .op .add [vv yI, .const 1], vv yN] bpBody
        [Enc.idxW b, BitVec.ofNat 64 i, cellA C oa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.size] (by decide)
        rfl (by decide) hcbp
        ⟨by simp, by simp +decide [Env.get, wapParams, ctxEnv], by simp +decide [Env.get, wapParams, ctxEnv],
          by simp +decide [sev, Env.get, wapParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [Env.get, wapParams, ctxEnv], trivial⟩
        (hBp H s b i hpre (by omega) (i + 1) (by omega))
    · rw [ite_eq_right (show ¬ (v.tag == ETag.lam) = true by simpa [ETag.lam] using htg)]
      cases same
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, wapParams, ctxEnv, boolW]) (fun h => absurd rfl h)
          (fun _ => ?_)
        show SpecR _ _ s (internAppE v args[i] >>= _) _
        refine specR_internAppI (C := ctxH C H) ra hok' hcI yAp (vv yV) (vv yA) v args[i] (by decide)
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp) (fun ap s1 => ?_)
        exact hrest ap s1 _ (by simp) (by simp) (by simp) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv])
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, wapParams, ctxEnv, boolW]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        refine specR_assignI yAp (vv yNo) (Enc.idxW nodes[i]!) (by decide) (by simp) ?_
        show SpecR _ _ s (pure nodes[i]! >>= _) _
        rw [pure_bind]
        exact hrest nodes[i]! s _ (by simp) (by simp) (by simp) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv]) (by simp +decide [Env.get, wapParams, ctxEnv])
          (by simp +decide [Env.get, wapParams, ctxEnv])

end

end ConPanqueque.T.WC
