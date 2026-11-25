import ConPanqueque.T.Core.ProjLit
import ConPanqueque.T.Core.PeelPis
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `reduceProjCore`: the projection rule on a reduced scrutinee

`proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the projection table (`tblFindP`): the scrutinee through `projLitToCtor`,
its head must be the table's constructor with the full spine and the level arity; `bvar 0` is interned (the
twin's default for `getD`), then the certificate at the verified mode (`projCert`). The answer is `optW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def rqE := ofString "rqe"
def rqT := ofString "rqt"
def rqQ := ofString "rqq"
def rqNf := ofString "rqnf"
def rqHh := ofString "rqhh"
def rqK := ofString "rqk"
def rqU := ofString "rqu"
def rqA := ofString "rqa"
def rqCt := ofString "rqct"
def rqNp := ofString "rqnp"
def rqLp := ofString "rqlp"
def rqLl := ofString "rqll"
def rqAl := ofString "rqal"
def rqB0 := ofString "rqb0"
def rqX := ofString "rqx"
def rqOk := ofString "rqok"

@[simp] theorem rq_rqE_ne_rqT : rqE ≠ rqT := by decide
@[simp] theorem rq_rqE_ne_rqQ : rqE ≠ rqQ := by decide
@[simp] theorem rq_rqE_ne_rqNf : rqE ≠ rqNf := by decide
@[simp] theorem rq_rqE_ne_rqHh : rqE ≠ rqHh := by decide
@[simp] theorem rq_rqE_ne_rqK : rqE ≠ rqK := by decide
@[simp] theorem rq_rqE_ne_rqU : rqE ≠ rqU := by decide
@[simp] theorem rq_rqE_ne_rqA : rqE ≠ rqA := by decide
@[simp] theorem rq_rqE_ne_rqCt : rqE ≠ rqCt := by decide
@[simp] theorem rq_rqE_ne_rqNp : rqE ≠ rqNp := by decide
@[simp] theorem rq_rqE_ne_rqLp : rqE ≠ rqLp := by decide
@[simp] theorem rq_rqE_ne_rqLl : rqE ≠ rqLl := by decide
@[simp] theorem rq_rqE_ne_rqAl : rqE ≠ rqAl := by decide
@[simp] theorem rq_rqE_ne_rqB0 : rqE ≠ rqB0 := by decide
@[simp] theorem rq_rqE_ne_rqX : rqE ≠ rqX := by decide
@[simp] theorem rq_rqE_ne_rqOk : rqE ≠ rqOk := by decide
@[simp] theorem rq_rqE_ne_lFl : rqE ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqE : lFl ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lDh : rqE ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqE : lDh ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lDt : rqE ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqE : lDt ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lDg : rqE ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqE : lDg ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lDi : rqE ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqE : lDi ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lRp : rqE ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqE : lRp ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lRn : rqE ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqE : lRn ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lFle : rqE ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqE : lFle ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lFls : rqE ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqE : lFls ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lDir : rqE ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqE : lDir ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_lKb : rqE ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqE : lKb ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_kFu : rqE ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqE : kFu ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_kD : rqE ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqE : kD ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_sN : rqE ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqE : sN ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_sI : rqE ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqE : sI ≠ rqE := by decide
@[simp] theorem rq_rqE_ne_sP : rqE ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqE : sP ≠ rqE := by decide
@[simp] theorem rq_rqT_ne_rqE : rqT ≠ rqE := by decide
@[simp] theorem rq_rqT_ne_rqQ : rqT ≠ rqQ := by decide
@[simp] theorem rq_rqT_ne_rqNf : rqT ≠ rqNf := by decide
@[simp] theorem rq_rqT_ne_rqHh : rqT ≠ rqHh := by decide
@[simp] theorem rq_rqT_ne_rqK : rqT ≠ rqK := by decide
@[simp] theorem rq_rqT_ne_rqU : rqT ≠ rqU := by decide
@[simp] theorem rq_rqT_ne_rqA : rqT ≠ rqA := by decide
@[simp] theorem rq_rqT_ne_rqCt : rqT ≠ rqCt := by decide
@[simp] theorem rq_rqT_ne_rqNp : rqT ≠ rqNp := by decide
@[simp] theorem rq_rqT_ne_rqLp : rqT ≠ rqLp := by decide
@[simp] theorem rq_rqT_ne_rqLl : rqT ≠ rqLl := by decide
@[simp] theorem rq_rqT_ne_rqAl : rqT ≠ rqAl := by decide
@[simp] theorem rq_rqT_ne_rqB0 : rqT ≠ rqB0 := by decide
@[simp] theorem rq_rqT_ne_rqX : rqT ≠ rqX := by decide
@[simp] theorem rq_rqT_ne_rqOk : rqT ≠ rqOk := by decide
@[simp] theorem rq_rqT_ne_lFl : rqT ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqT : lFl ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lDh : rqT ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqT : lDh ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lDt : rqT ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqT : lDt ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lDg : rqT ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqT : lDg ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lDi : rqT ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqT : lDi ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lRp : rqT ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqT : lRp ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lRn : rqT ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqT : lRn ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lFle : rqT ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqT : lFle ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lFls : rqT ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqT : lFls ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lDir : rqT ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqT : lDir ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_lKb : rqT ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqT : lKb ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_kFu : rqT ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqT : kFu ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_kD : rqT ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqT : kD ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_sN : rqT ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqT : sN ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_sI : rqT ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqT : sI ≠ rqT := by decide
@[simp] theorem rq_rqT_ne_sP : rqT ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqT : sP ≠ rqT := by decide
@[simp] theorem rq_rqQ_ne_rqE : rqQ ≠ rqE := by decide
@[simp] theorem rq_rqQ_ne_rqT : rqQ ≠ rqT := by decide
@[simp] theorem rq_rqQ_ne_rqNf : rqQ ≠ rqNf := by decide
@[simp] theorem rq_rqQ_ne_rqHh : rqQ ≠ rqHh := by decide
@[simp] theorem rq_rqQ_ne_rqK : rqQ ≠ rqK := by decide
@[simp] theorem rq_rqQ_ne_rqU : rqQ ≠ rqU := by decide
@[simp] theorem rq_rqQ_ne_rqA : rqQ ≠ rqA := by decide
@[simp] theorem rq_rqQ_ne_rqCt : rqQ ≠ rqCt := by decide
@[simp] theorem rq_rqQ_ne_rqNp : rqQ ≠ rqNp := by decide
@[simp] theorem rq_rqQ_ne_rqLp : rqQ ≠ rqLp := by decide
@[simp] theorem rq_rqQ_ne_rqLl : rqQ ≠ rqLl := by decide
@[simp] theorem rq_rqQ_ne_rqAl : rqQ ≠ rqAl := by decide
@[simp] theorem rq_rqQ_ne_rqB0 : rqQ ≠ rqB0 := by decide
@[simp] theorem rq_rqQ_ne_rqX : rqQ ≠ rqX := by decide
@[simp] theorem rq_rqQ_ne_rqOk : rqQ ≠ rqOk := by decide
@[simp] theorem rq_rqQ_ne_lFl : rqQ ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqQ : lFl ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lDh : rqQ ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqQ : lDh ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lDt : rqQ ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqQ : lDt ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lDg : rqQ ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqQ : lDg ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lDi : rqQ ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqQ : lDi ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lRp : rqQ ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqQ : lRp ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lRn : rqQ ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqQ : lRn ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lFle : rqQ ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqQ : lFle ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lFls : rqQ ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqQ : lFls ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lDir : rqQ ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqQ : lDir ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_lKb : rqQ ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqQ : lKb ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_kFu : rqQ ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqQ : kFu ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_kD : rqQ ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqQ : kD ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_sN : rqQ ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqQ : sN ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_sI : rqQ ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqQ : sI ≠ rqQ := by decide
@[simp] theorem rq_rqQ_ne_sP : rqQ ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqQ : sP ≠ rqQ := by decide
@[simp] theorem rq_rqNf_ne_rqE : rqNf ≠ rqE := by decide
@[simp] theorem rq_rqNf_ne_rqT : rqNf ≠ rqT := by decide
@[simp] theorem rq_rqNf_ne_rqQ : rqNf ≠ rqQ := by decide
@[simp] theorem rq_rqNf_ne_rqHh : rqNf ≠ rqHh := by decide
@[simp] theorem rq_rqNf_ne_rqK : rqNf ≠ rqK := by decide
@[simp] theorem rq_rqNf_ne_rqU : rqNf ≠ rqU := by decide
@[simp] theorem rq_rqNf_ne_rqA : rqNf ≠ rqA := by decide
@[simp] theorem rq_rqNf_ne_rqCt : rqNf ≠ rqCt := by decide
@[simp] theorem rq_rqNf_ne_rqNp : rqNf ≠ rqNp := by decide
@[simp] theorem rq_rqNf_ne_rqLp : rqNf ≠ rqLp := by decide
@[simp] theorem rq_rqNf_ne_rqLl : rqNf ≠ rqLl := by decide
@[simp] theorem rq_rqNf_ne_rqAl : rqNf ≠ rqAl := by decide
@[simp] theorem rq_rqNf_ne_rqB0 : rqNf ≠ rqB0 := by decide
@[simp] theorem rq_rqNf_ne_rqX : rqNf ≠ rqX := by decide
@[simp] theorem rq_rqNf_ne_rqOk : rqNf ≠ rqOk := by decide
@[simp] theorem rq_rqNf_ne_lFl : rqNf ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqNf : lFl ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lDh : rqNf ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqNf : lDh ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lDt : rqNf ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqNf : lDt ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lDg : rqNf ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqNf : lDg ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lDi : rqNf ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqNf : lDi ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lRp : rqNf ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqNf : lRp ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lRn : rqNf ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqNf : lRn ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lFle : rqNf ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqNf : lFle ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lFls : rqNf ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqNf : lFls ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lDir : rqNf ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqNf : lDir ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_lKb : rqNf ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqNf : lKb ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_kFu : rqNf ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqNf : kFu ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_kD : rqNf ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqNf : kD ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_sN : rqNf ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqNf : sN ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_sI : rqNf ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqNf : sI ≠ rqNf := by decide
@[simp] theorem rq_rqNf_ne_sP : rqNf ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqNf : sP ≠ rqNf := by decide
@[simp] theorem rq_rqHh_ne_rqE : rqHh ≠ rqE := by decide
@[simp] theorem rq_rqHh_ne_rqT : rqHh ≠ rqT := by decide
@[simp] theorem rq_rqHh_ne_rqQ : rqHh ≠ rqQ := by decide
@[simp] theorem rq_rqHh_ne_rqNf : rqHh ≠ rqNf := by decide
@[simp] theorem rq_rqHh_ne_rqK : rqHh ≠ rqK := by decide
@[simp] theorem rq_rqHh_ne_rqU : rqHh ≠ rqU := by decide
@[simp] theorem rq_rqHh_ne_rqA : rqHh ≠ rqA := by decide
@[simp] theorem rq_rqHh_ne_rqCt : rqHh ≠ rqCt := by decide
@[simp] theorem rq_rqHh_ne_rqNp : rqHh ≠ rqNp := by decide
@[simp] theorem rq_rqHh_ne_rqLp : rqHh ≠ rqLp := by decide
@[simp] theorem rq_rqHh_ne_rqLl : rqHh ≠ rqLl := by decide
@[simp] theorem rq_rqHh_ne_rqAl : rqHh ≠ rqAl := by decide
@[simp] theorem rq_rqHh_ne_rqB0 : rqHh ≠ rqB0 := by decide
@[simp] theorem rq_rqHh_ne_rqX : rqHh ≠ rqX := by decide
@[simp] theorem rq_rqHh_ne_rqOk : rqHh ≠ rqOk := by decide
@[simp] theorem rq_rqHh_ne_lFl : rqHh ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqHh : lFl ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lDh : rqHh ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqHh : lDh ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lDt : rqHh ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqHh : lDt ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lDg : rqHh ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqHh : lDg ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lDi : rqHh ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqHh : lDi ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lRp : rqHh ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqHh : lRp ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lRn : rqHh ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqHh : lRn ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lFle : rqHh ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqHh : lFle ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lFls : rqHh ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqHh : lFls ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lDir : rqHh ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqHh : lDir ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_lKb : rqHh ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqHh : lKb ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_kFu : rqHh ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqHh : kFu ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_kD : rqHh ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqHh : kD ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_sN : rqHh ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqHh : sN ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_sI : rqHh ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqHh : sI ≠ rqHh := by decide
@[simp] theorem rq_rqHh_ne_sP : rqHh ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqHh : sP ≠ rqHh := by decide
@[simp] theorem rq_rqK_ne_rqE : rqK ≠ rqE := by decide
@[simp] theorem rq_rqK_ne_rqT : rqK ≠ rqT := by decide
@[simp] theorem rq_rqK_ne_rqQ : rqK ≠ rqQ := by decide
@[simp] theorem rq_rqK_ne_rqNf : rqK ≠ rqNf := by decide
@[simp] theorem rq_rqK_ne_rqHh : rqK ≠ rqHh := by decide
@[simp] theorem rq_rqK_ne_rqU : rqK ≠ rqU := by decide
@[simp] theorem rq_rqK_ne_rqA : rqK ≠ rqA := by decide
@[simp] theorem rq_rqK_ne_rqCt : rqK ≠ rqCt := by decide
@[simp] theorem rq_rqK_ne_rqNp : rqK ≠ rqNp := by decide
@[simp] theorem rq_rqK_ne_rqLp : rqK ≠ rqLp := by decide
@[simp] theorem rq_rqK_ne_rqLl : rqK ≠ rqLl := by decide
@[simp] theorem rq_rqK_ne_rqAl : rqK ≠ rqAl := by decide
@[simp] theorem rq_rqK_ne_rqB0 : rqK ≠ rqB0 := by decide
@[simp] theorem rq_rqK_ne_rqX : rqK ≠ rqX := by decide
@[simp] theorem rq_rqK_ne_rqOk : rqK ≠ rqOk := by decide
@[simp] theorem rq_rqK_ne_lFl : rqK ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqK : lFl ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lDh : rqK ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqK : lDh ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lDt : rqK ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqK : lDt ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lDg : rqK ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqK : lDg ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lDi : rqK ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqK : lDi ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lRp : rqK ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqK : lRp ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lRn : rqK ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqK : lRn ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lFle : rqK ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqK : lFle ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lFls : rqK ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqK : lFls ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lDir : rqK ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqK : lDir ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_lKb : rqK ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqK : lKb ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_kFu : rqK ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqK : kFu ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_kD : rqK ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqK : kD ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_sN : rqK ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqK : sN ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_sI : rqK ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqK : sI ≠ rqK := by decide
@[simp] theorem rq_rqK_ne_sP : rqK ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqK : sP ≠ rqK := by decide
@[simp] theorem rq_rqU_ne_rqE : rqU ≠ rqE := by decide
@[simp] theorem rq_rqU_ne_rqT : rqU ≠ rqT := by decide
@[simp] theorem rq_rqU_ne_rqQ : rqU ≠ rqQ := by decide
@[simp] theorem rq_rqU_ne_rqNf : rqU ≠ rqNf := by decide
@[simp] theorem rq_rqU_ne_rqHh : rqU ≠ rqHh := by decide
@[simp] theorem rq_rqU_ne_rqK : rqU ≠ rqK := by decide
@[simp] theorem rq_rqU_ne_rqA : rqU ≠ rqA := by decide
@[simp] theorem rq_rqU_ne_rqCt : rqU ≠ rqCt := by decide
@[simp] theorem rq_rqU_ne_rqNp : rqU ≠ rqNp := by decide
@[simp] theorem rq_rqU_ne_rqLp : rqU ≠ rqLp := by decide
@[simp] theorem rq_rqU_ne_rqLl : rqU ≠ rqLl := by decide
@[simp] theorem rq_rqU_ne_rqAl : rqU ≠ rqAl := by decide
@[simp] theorem rq_rqU_ne_rqB0 : rqU ≠ rqB0 := by decide
@[simp] theorem rq_rqU_ne_rqX : rqU ≠ rqX := by decide
@[simp] theorem rq_rqU_ne_rqOk : rqU ≠ rqOk := by decide
@[simp] theorem rq_rqU_ne_lFl : rqU ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqU : lFl ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lDh : rqU ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqU : lDh ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lDt : rqU ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqU : lDt ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lDg : rqU ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqU : lDg ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lDi : rqU ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqU : lDi ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lRp : rqU ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqU : lRp ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lRn : rqU ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqU : lRn ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lFle : rqU ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqU : lFle ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lFls : rqU ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqU : lFls ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lDir : rqU ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqU : lDir ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_lKb : rqU ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqU : lKb ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_kFu : rqU ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqU : kFu ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_kD : rqU ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqU : kD ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_sN : rqU ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqU : sN ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_sI : rqU ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqU : sI ≠ rqU := by decide
@[simp] theorem rq_rqU_ne_sP : rqU ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqU : sP ≠ rqU := by decide
@[simp] theorem rq_rqA_ne_rqE : rqA ≠ rqE := by decide
@[simp] theorem rq_rqA_ne_rqT : rqA ≠ rqT := by decide
@[simp] theorem rq_rqA_ne_rqQ : rqA ≠ rqQ := by decide
@[simp] theorem rq_rqA_ne_rqNf : rqA ≠ rqNf := by decide
@[simp] theorem rq_rqA_ne_rqHh : rqA ≠ rqHh := by decide
@[simp] theorem rq_rqA_ne_rqK : rqA ≠ rqK := by decide
@[simp] theorem rq_rqA_ne_rqU : rqA ≠ rqU := by decide
@[simp] theorem rq_rqA_ne_rqCt : rqA ≠ rqCt := by decide
@[simp] theorem rq_rqA_ne_rqNp : rqA ≠ rqNp := by decide
@[simp] theorem rq_rqA_ne_rqLp : rqA ≠ rqLp := by decide
@[simp] theorem rq_rqA_ne_rqLl : rqA ≠ rqLl := by decide
@[simp] theorem rq_rqA_ne_rqAl : rqA ≠ rqAl := by decide
@[simp] theorem rq_rqA_ne_rqB0 : rqA ≠ rqB0 := by decide
@[simp] theorem rq_rqA_ne_rqX : rqA ≠ rqX := by decide
@[simp] theorem rq_rqA_ne_rqOk : rqA ≠ rqOk := by decide
@[simp] theorem rq_rqA_ne_lFl : rqA ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqA : lFl ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lDh : rqA ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqA : lDh ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lDt : rqA ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqA : lDt ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lDg : rqA ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqA : lDg ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lDi : rqA ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqA : lDi ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lRp : rqA ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqA : lRp ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lRn : rqA ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqA : lRn ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lFle : rqA ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqA : lFle ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lFls : rqA ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqA : lFls ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lDir : rqA ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqA : lDir ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_lKb : rqA ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqA : lKb ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_kFu : rqA ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqA : kFu ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_kD : rqA ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqA : kD ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_sN : rqA ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqA : sN ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_sI : rqA ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqA : sI ≠ rqA := by decide
@[simp] theorem rq_rqA_ne_sP : rqA ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqA : sP ≠ rqA := by decide
@[simp] theorem rq_rqCt_ne_rqE : rqCt ≠ rqE := by decide
@[simp] theorem rq_rqCt_ne_rqT : rqCt ≠ rqT := by decide
@[simp] theorem rq_rqCt_ne_rqQ : rqCt ≠ rqQ := by decide
@[simp] theorem rq_rqCt_ne_rqNf : rqCt ≠ rqNf := by decide
@[simp] theorem rq_rqCt_ne_rqHh : rqCt ≠ rqHh := by decide
@[simp] theorem rq_rqCt_ne_rqK : rqCt ≠ rqK := by decide
@[simp] theorem rq_rqCt_ne_rqU : rqCt ≠ rqU := by decide
@[simp] theorem rq_rqCt_ne_rqA : rqCt ≠ rqA := by decide
@[simp] theorem rq_rqCt_ne_rqNp : rqCt ≠ rqNp := by decide
@[simp] theorem rq_rqCt_ne_rqLp : rqCt ≠ rqLp := by decide
@[simp] theorem rq_rqCt_ne_rqLl : rqCt ≠ rqLl := by decide
@[simp] theorem rq_rqCt_ne_rqAl : rqCt ≠ rqAl := by decide
@[simp] theorem rq_rqCt_ne_rqB0 : rqCt ≠ rqB0 := by decide
@[simp] theorem rq_rqCt_ne_rqX : rqCt ≠ rqX := by decide
@[simp] theorem rq_rqCt_ne_rqOk : rqCt ≠ rqOk := by decide
@[simp] theorem rq_rqCt_ne_lFl : rqCt ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqCt : lFl ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lDh : rqCt ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqCt : lDh ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lDt : rqCt ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqCt : lDt ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lDg : rqCt ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqCt : lDg ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lDi : rqCt ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqCt : lDi ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lRp : rqCt ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqCt : lRp ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lRn : rqCt ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqCt : lRn ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lFle : rqCt ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqCt : lFle ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lFls : rqCt ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqCt : lFls ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lDir : rqCt ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqCt : lDir ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_lKb : rqCt ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqCt : lKb ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_kFu : rqCt ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqCt : kFu ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_kD : rqCt ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqCt : kD ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_sN : rqCt ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqCt : sN ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_sI : rqCt ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqCt : sI ≠ rqCt := by decide
@[simp] theorem rq_rqCt_ne_sP : rqCt ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqCt : sP ≠ rqCt := by decide
@[simp] theorem rq_rqNp_ne_rqE : rqNp ≠ rqE := by decide
@[simp] theorem rq_rqNp_ne_rqT : rqNp ≠ rqT := by decide
@[simp] theorem rq_rqNp_ne_rqQ : rqNp ≠ rqQ := by decide
@[simp] theorem rq_rqNp_ne_rqNf : rqNp ≠ rqNf := by decide
@[simp] theorem rq_rqNp_ne_rqHh : rqNp ≠ rqHh := by decide
@[simp] theorem rq_rqNp_ne_rqK : rqNp ≠ rqK := by decide
@[simp] theorem rq_rqNp_ne_rqU : rqNp ≠ rqU := by decide
@[simp] theorem rq_rqNp_ne_rqA : rqNp ≠ rqA := by decide
@[simp] theorem rq_rqNp_ne_rqCt : rqNp ≠ rqCt := by decide
@[simp] theorem rq_rqNp_ne_rqLp : rqNp ≠ rqLp := by decide
@[simp] theorem rq_rqNp_ne_rqLl : rqNp ≠ rqLl := by decide
@[simp] theorem rq_rqNp_ne_rqAl : rqNp ≠ rqAl := by decide
@[simp] theorem rq_rqNp_ne_rqB0 : rqNp ≠ rqB0 := by decide
@[simp] theorem rq_rqNp_ne_rqX : rqNp ≠ rqX := by decide
@[simp] theorem rq_rqNp_ne_rqOk : rqNp ≠ rqOk := by decide
@[simp] theorem rq_rqNp_ne_lFl : rqNp ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqNp : lFl ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lDh : rqNp ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqNp : lDh ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lDt : rqNp ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqNp : lDt ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lDg : rqNp ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqNp : lDg ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lDi : rqNp ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqNp : lDi ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lRp : rqNp ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqNp : lRp ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lRn : rqNp ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqNp : lRn ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lFle : rqNp ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqNp : lFle ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lFls : rqNp ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqNp : lFls ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lDir : rqNp ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqNp : lDir ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_lKb : rqNp ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqNp : lKb ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_kFu : rqNp ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqNp : kFu ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_kD : rqNp ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqNp : kD ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_sN : rqNp ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqNp : sN ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_sI : rqNp ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqNp : sI ≠ rqNp := by decide
@[simp] theorem rq_rqNp_ne_sP : rqNp ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqNp : sP ≠ rqNp := by decide
@[simp] theorem rq_rqLp_ne_rqE : rqLp ≠ rqE := by decide
@[simp] theorem rq_rqLp_ne_rqT : rqLp ≠ rqT := by decide
@[simp] theorem rq_rqLp_ne_rqQ : rqLp ≠ rqQ := by decide
@[simp] theorem rq_rqLp_ne_rqNf : rqLp ≠ rqNf := by decide
@[simp] theorem rq_rqLp_ne_rqHh : rqLp ≠ rqHh := by decide
@[simp] theorem rq_rqLp_ne_rqK : rqLp ≠ rqK := by decide
@[simp] theorem rq_rqLp_ne_rqU : rqLp ≠ rqU := by decide
@[simp] theorem rq_rqLp_ne_rqA : rqLp ≠ rqA := by decide
@[simp] theorem rq_rqLp_ne_rqCt : rqLp ≠ rqCt := by decide
@[simp] theorem rq_rqLp_ne_rqNp : rqLp ≠ rqNp := by decide
@[simp] theorem rq_rqLp_ne_rqLl : rqLp ≠ rqLl := by decide
@[simp] theorem rq_rqLp_ne_rqAl : rqLp ≠ rqAl := by decide
@[simp] theorem rq_rqLp_ne_rqB0 : rqLp ≠ rqB0 := by decide
@[simp] theorem rq_rqLp_ne_rqX : rqLp ≠ rqX := by decide
@[simp] theorem rq_rqLp_ne_rqOk : rqLp ≠ rqOk := by decide
@[simp] theorem rq_rqLp_ne_lFl : rqLp ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqLp : lFl ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lDh : rqLp ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqLp : lDh ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lDt : rqLp ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqLp : lDt ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lDg : rqLp ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqLp : lDg ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lDi : rqLp ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqLp : lDi ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lRp : rqLp ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqLp : lRp ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lRn : rqLp ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqLp : lRn ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lFle : rqLp ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqLp : lFle ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lFls : rqLp ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqLp : lFls ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lDir : rqLp ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqLp : lDir ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_lKb : rqLp ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqLp : lKb ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_kFu : rqLp ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqLp : kFu ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_kD : rqLp ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqLp : kD ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_sN : rqLp ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqLp : sN ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_sI : rqLp ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqLp : sI ≠ rqLp := by decide
@[simp] theorem rq_rqLp_ne_sP : rqLp ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqLp : sP ≠ rqLp := by decide
@[simp] theorem rq_rqLl_ne_rqE : rqLl ≠ rqE := by decide
@[simp] theorem rq_rqLl_ne_rqT : rqLl ≠ rqT := by decide
@[simp] theorem rq_rqLl_ne_rqQ : rqLl ≠ rqQ := by decide
@[simp] theorem rq_rqLl_ne_rqNf : rqLl ≠ rqNf := by decide
@[simp] theorem rq_rqLl_ne_rqHh : rqLl ≠ rqHh := by decide
@[simp] theorem rq_rqLl_ne_rqK : rqLl ≠ rqK := by decide
@[simp] theorem rq_rqLl_ne_rqU : rqLl ≠ rqU := by decide
@[simp] theorem rq_rqLl_ne_rqA : rqLl ≠ rqA := by decide
@[simp] theorem rq_rqLl_ne_rqCt : rqLl ≠ rqCt := by decide
@[simp] theorem rq_rqLl_ne_rqNp : rqLl ≠ rqNp := by decide
@[simp] theorem rq_rqLl_ne_rqLp : rqLl ≠ rqLp := by decide
@[simp] theorem rq_rqLl_ne_rqAl : rqLl ≠ rqAl := by decide
@[simp] theorem rq_rqLl_ne_rqB0 : rqLl ≠ rqB0 := by decide
@[simp] theorem rq_rqLl_ne_rqX : rqLl ≠ rqX := by decide
@[simp] theorem rq_rqLl_ne_rqOk : rqLl ≠ rqOk := by decide
@[simp] theorem rq_rqLl_ne_lFl : rqLl ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqLl : lFl ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lDh : rqLl ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqLl : lDh ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lDt : rqLl ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqLl : lDt ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lDg : rqLl ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqLl : lDg ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lDi : rqLl ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqLl : lDi ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lRp : rqLl ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqLl : lRp ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lRn : rqLl ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqLl : lRn ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lFle : rqLl ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqLl : lFle ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lFls : rqLl ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqLl : lFls ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lDir : rqLl ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqLl : lDir ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_lKb : rqLl ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqLl : lKb ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_kFu : rqLl ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqLl : kFu ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_kD : rqLl ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqLl : kD ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_sN : rqLl ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqLl : sN ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_sI : rqLl ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqLl : sI ≠ rqLl := by decide
@[simp] theorem rq_rqLl_ne_sP : rqLl ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqLl : sP ≠ rqLl := by decide
@[simp] theorem rq_rqAl_ne_rqE : rqAl ≠ rqE := by decide
@[simp] theorem rq_rqAl_ne_rqT : rqAl ≠ rqT := by decide
@[simp] theorem rq_rqAl_ne_rqQ : rqAl ≠ rqQ := by decide
@[simp] theorem rq_rqAl_ne_rqNf : rqAl ≠ rqNf := by decide
@[simp] theorem rq_rqAl_ne_rqHh : rqAl ≠ rqHh := by decide
@[simp] theorem rq_rqAl_ne_rqK : rqAl ≠ rqK := by decide
@[simp] theorem rq_rqAl_ne_rqU : rqAl ≠ rqU := by decide
@[simp] theorem rq_rqAl_ne_rqA : rqAl ≠ rqA := by decide
@[simp] theorem rq_rqAl_ne_rqCt : rqAl ≠ rqCt := by decide
@[simp] theorem rq_rqAl_ne_rqNp : rqAl ≠ rqNp := by decide
@[simp] theorem rq_rqAl_ne_rqLp : rqAl ≠ rqLp := by decide
@[simp] theorem rq_rqAl_ne_rqLl : rqAl ≠ rqLl := by decide
@[simp] theorem rq_rqAl_ne_rqB0 : rqAl ≠ rqB0 := by decide
@[simp] theorem rq_rqAl_ne_rqX : rqAl ≠ rqX := by decide
@[simp] theorem rq_rqAl_ne_rqOk : rqAl ≠ rqOk := by decide
@[simp] theorem rq_rqAl_ne_lFl : rqAl ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqAl : lFl ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lDh : rqAl ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqAl : lDh ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lDt : rqAl ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqAl : lDt ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lDg : rqAl ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqAl : lDg ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lDi : rqAl ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqAl : lDi ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lRp : rqAl ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqAl : lRp ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lRn : rqAl ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqAl : lRn ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lFle : rqAl ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqAl : lFle ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lFls : rqAl ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqAl : lFls ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lDir : rqAl ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqAl : lDir ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_lKb : rqAl ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqAl : lKb ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_kFu : rqAl ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqAl : kFu ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_kD : rqAl ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqAl : kD ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_sN : rqAl ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqAl : sN ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_sI : rqAl ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqAl : sI ≠ rqAl := by decide
@[simp] theorem rq_rqAl_ne_sP : rqAl ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqAl : sP ≠ rqAl := by decide
@[simp] theorem rq_rqB0_ne_rqE : rqB0 ≠ rqE := by decide
@[simp] theorem rq_rqB0_ne_rqT : rqB0 ≠ rqT := by decide
@[simp] theorem rq_rqB0_ne_rqQ : rqB0 ≠ rqQ := by decide
@[simp] theorem rq_rqB0_ne_rqNf : rqB0 ≠ rqNf := by decide
@[simp] theorem rq_rqB0_ne_rqHh : rqB0 ≠ rqHh := by decide
@[simp] theorem rq_rqB0_ne_rqK : rqB0 ≠ rqK := by decide
@[simp] theorem rq_rqB0_ne_rqU : rqB0 ≠ rqU := by decide
@[simp] theorem rq_rqB0_ne_rqA : rqB0 ≠ rqA := by decide
@[simp] theorem rq_rqB0_ne_rqCt : rqB0 ≠ rqCt := by decide
@[simp] theorem rq_rqB0_ne_rqNp : rqB0 ≠ rqNp := by decide
@[simp] theorem rq_rqB0_ne_rqLp : rqB0 ≠ rqLp := by decide
@[simp] theorem rq_rqB0_ne_rqLl : rqB0 ≠ rqLl := by decide
@[simp] theorem rq_rqB0_ne_rqAl : rqB0 ≠ rqAl := by decide
@[simp] theorem rq_rqB0_ne_rqX : rqB0 ≠ rqX := by decide
@[simp] theorem rq_rqB0_ne_rqOk : rqB0 ≠ rqOk := by decide
@[simp] theorem rq_rqB0_ne_lFl : rqB0 ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqB0 : lFl ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lDh : rqB0 ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqB0 : lDh ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lDt : rqB0 ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqB0 : lDt ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lDg : rqB0 ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqB0 : lDg ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lDi : rqB0 ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqB0 : lDi ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lRp : rqB0 ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqB0 : lRp ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lRn : rqB0 ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqB0 : lRn ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lFle : rqB0 ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqB0 : lFle ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lFls : rqB0 ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqB0 : lFls ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lDir : rqB0 ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqB0 : lDir ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_lKb : rqB0 ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqB0 : lKb ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_kFu : rqB0 ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqB0 : kFu ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_kD : rqB0 ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqB0 : kD ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_sN : rqB0 ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqB0 : sN ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_sI : rqB0 ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqB0 : sI ≠ rqB0 := by decide
@[simp] theorem rq_rqB0_ne_sP : rqB0 ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqB0 : sP ≠ rqB0 := by decide
@[simp] theorem rq_rqX_ne_rqE : rqX ≠ rqE := by decide
@[simp] theorem rq_rqX_ne_rqT : rqX ≠ rqT := by decide
@[simp] theorem rq_rqX_ne_rqQ : rqX ≠ rqQ := by decide
@[simp] theorem rq_rqX_ne_rqNf : rqX ≠ rqNf := by decide
@[simp] theorem rq_rqX_ne_rqHh : rqX ≠ rqHh := by decide
@[simp] theorem rq_rqX_ne_rqK : rqX ≠ rqK := by decide
@[simp] theorem rq_rqX_ne_rqU : rqX ≠ rqU := by decide
@[simp] theorem rq_rqX_ne_rqA : rqX ≠ rqA := by decide
@[simp] theorem rq_rqX_ne_rqCt : rqX ≠ rqCt := by decide
@[simp] theorem rq_rqX_ne_rqNp : rqX ≠ rqNp := by decide
@[simp] theorem rq_rqX_ne_rqLp : rqX ≠ rqLp := by decide
@[simp] theorem rq_rqX_ne_rqLl : rqX ≠ rqLl := by decide
@[simp] theorem rq_rqX_ne_rqAl : rqX ≠ rqAl := by decide
@[simp] theorem rq_rqX_ne_rqB0 : rqX ≠ rqB0 := by decide
@[simp] theorem rq_rqX_ne_rqOk : rqX ≠ rqOk := by decide
@[simp] theorem rq_rqX_ne_lFl : rqX ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqX : lFl ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lDh : rqX ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqX : lDh ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lDt : rqX ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqX : lDt ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lDg : rqX ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqX : lDg ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lDi : rqX ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqX : lDi ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lRp : rqX ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqX : lRp ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lRn : rqX ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqX : lRn ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lFle : rqX ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqX : lFle ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lFls : rqX ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqX : lFls ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lDir : rqX ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqX : lDir ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_lKb : rqX ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqX : lKb ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_kFu : rqX ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqX : kFu ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_kD : rqX ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqX : kD ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_sN : rqX ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqX : sN ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_sI : rqX ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqX : sI ≠ rqX := by decide
@[simp] theorem rq_rqX_ne_sP : rqX ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqX : sP ≠ rqX := by decide
@[simp] theorem rq_rqOk_ne_rqE : rqOk ≠ rqE := by decide
@[simp] theorem rq_rqOk_ne_rqT : rqOk ≠ rqT := by decide
@[simp] theorem rq_rqOk_ne_rqQ : rqOk ≠ rqQ := by decide
@[simp] theorem rq_rqOk_ne_rqNf : rqOk ≠ rqNf := by decide
@[simp] theorem rq_rqOk_ne_rqHh : rqOk ≠ rqHh := by decide
@[simp] theorem rq_rqOk_ne_rqK : rqOk ≠ rqK := by decide
@[simp] theorem rq_rqOk_ne_rqU : rqOk ≠ rqU := by decide
@[simp] theorem rq_rqOk_ne_rqA : rqOk ≠ rqA := by decide
@[simp] theorem rq_rqOk_ne_rqCt : rqOk ≠ rqCt := by decide
@[simp] theorem rq_rqOk_ne_rqNp : rqOk ≠ rqNp := by decide
@[simp] theorem rq_rqOk_ne_rqLp : rqOk ≠ rqLp := by decide
@[simp] theorem rq_rqOk_ne_rqLl : rqOk ≠ rqLl := by decide
@[simp] theorem rq_rqOk_ne_rqAl : rqOk ≠ rqAl := by decide
@[simp] theorem rq_rqOk_ne_rqB0 : rqOk ≠ rqB0 := by decide
@[simp] theorem rq_rqOk_ne_rqX : rqOk ≠ rqX := by decide
@[simp] theorem rq_rqOk_ne_lFl : rqOk ≠ lFl := by decide
@[simp] theorem rq_lFl_ne_rqOk : lFl ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lDh : rqOk ≠ lDh := by decide
@[simp] theorem rq_lDh_ne_rqOk : lDh ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lDt : rqOk ≠ lDt := by decide
@[simp] theorem rq_lDt_ne_rqOk : lDt ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lDg : rqOk ≠ lDg := by decide
@[simp] theorem rq_lDg_ne_rqOk : lDg ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lDi : rqOk ≠ lDi := by decide
@[simp] theorem rq_lDi_ne_rqOk : lDi ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lRp : rqOk ≠ lRp := by decide
@[simp] theorem rq_lRp_ne_rqOk : lRp ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lRn : rqOk ≠ lRn := by decide
@[simp] theorem rq_lRn_ne_rqOk : lRn ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lFle : rqOk ≠ lFle := by decide
@[simp] theorem rq_lFle_ne_rqOk : lFle ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lFls : rqOk ≠ lFls := by decide
@[simp] theorem rq_lFls_ne_rqOk : lFls ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lDir : rqOk ≠ lDir := by decide
@[simp] theorem rq_lDir_ne_rqOk : lDir ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_lKb : rqOk ≠ lKb := by decide
@[simp] theorem rq_lKb_ne_rqOk : lKb ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_kFu : rqOk ≠ kFu := by decide
@[simp] theorem rq_kFu_ne_rqOk : kFu ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_kD : rqOk ≠ kD := by decide
@[simp] theorem rq_kD_ne_rqOk : kD ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_sN : rqOk ≠ sN := by decide
@[simp] theorem rq_sN_ne_rqOk : sN ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_sI : rqOk ≠ sI := by decide
@[simp] theorem rq_sI_ne_rqOk : sI ≠ rqOk := by decide
@[simp] theorem rq_rqOk_ne_sP : rqOk ≠ sP := by decide
@[simp] theorem rq_sP_ne_rqOk : sP ≠ rqOk := by decide

/-- `KB[0] := en; x := memoGet(projection-table table, 1); rest`: the twin's `fe.findTable? n` (pure). -/
def tblFindP (C : Ctx) (x : MlS) (en : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) en)
    (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG .tbl), .const 1]) rest)

/-- The fire certificate as the mode runs it: `projCert` at the verified mode, nothing at the trusted one. -/
def rpcCert (v : Bool) : ProgHOL 64 :=
  if v then
    .seq (.call (some (some (.local, rqOk), none)) fPc [vv rqK, vv rqAl])
      (.ite (vv rqOk) (.return (.op .add [vv rqX, .const 1])) (.return (.const 0)))
  else .return (.op .add [vv rqX, .const 1])

def rpcLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, rqE, rqT, rqQ, rqNf, rqHh, rqK, rqU, rqA, rqCt, rqNp,
  rqLp, rqLl, rqAl, rqB0, rqX, rqOk]

def rpcCore (v : Bool) (C : Ctx) : ProgHOL 64 :=
  (.seq (.call (some (some (.local, rqE), none)) fPl [vv kFu, vv kD, vv sP])
  (tblFindP C rqT (vv sN)
  (.ite (.cmp .equal (vv rqT) (.const 0)) (.return (.const 0))
  (.seq (.assign .local rqQ (.op .sub [vv rqT, .const 1]))
  (.seq (.assign .local rqNf (.load .one (.op .add [vv rqQ, .const 32])))
  (.ite (.cmp .lower (vv sI) (vv rqNf))
  (.seq (.call (some (some (.local, rqHh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv rqE])
  (.ite (tagIsE rqHh 3)
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv rqHh))
  (.seq eViewP
  (.seq (.assign .local rqK (.load .one (vv lRp)))
  (.seq (.assign .local rqU (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, rqA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv rqE])
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv rqU))
  (.seq lsViewP
  (.seq (.assign .local rqCt (.load .one (.op .add [vv rqQ, .const 24])))
  (.seq (.assign .local rqNp (.load .one (.op .add [vv rqQ, .const 16])))
  (.seq (.assign .local rqLp (.load .one (.op .add [vv rqQ, .const 8])))
  (.seq (.assign .local rqLl (.load .one (vv rqLp)))
  (.seq (.assign .local rqAl (.load .one (vv rqA)))
  (.ite (.cmp .notEqual (vv rqK) (vv rqCt)) (.return (.const 0))
  (.ite (.cmp .notEqual (vv rqAl) (.op .add [vv rqNp, vv rqNf])) (.return (.const 0))
  (.ite (.cmp .notEqual (vv lRn) (vv rqLl)) (.return (.const 0))
  (.seq (.call (some (some (.local, rqB0), none)) fInternBVar [.const 0])
  (.seq (.assign .local rqX (.load .one (.op .add [vv rqA, .shift .lsl (.op .add [.op .add [vv rqNp, vv sI], .const 1]) (.const 3)])))
  (rpcCert v))))))))))))))))))))
  (.return (.const 0))))
  (.return (.const 0))))))))

def rpcBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue rpcLocals (rpcCore v C)

section
variable {σ : Type}

theorem specR_tblFindI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (en : ExpHOL 64) (n : NIdx) (hx : x ∈ D) (hen : sev Γ en = some (Enc.idxW n))
    (hkb : Γ.get lKb = some C.KB)
    (hk : SpecR (Inv C s ((x, optWG id C.tblM[n]?) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (tblFindP C x en rest) s m R := by
  refine specR_storeKBI hok 0 (by decide) en (Enc.idxW n) hen hkb ?_
  refine specR_congr (m' := (pure C.tblM[n]? : AM (Option (BitVec 64))) >>= fun _ => m) rfl ?_
  exact specR_memoGetGI (K := NIdx) (V := BitVec 64) encNI_inj (C.mG .tbl) (C.mg .tbl) C.tblM n _ rfl
    (fun u hu => hu.env.2.2.1) hcodeG hcodeP x (.const (C.mG .tbl)) (.const 1) hx rfl rfl (by simp [encNI])
    (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW n) (by simp)) hk

theorem tbl_rel {C : Ctx} (hok : CtxOK C) (n : NIdx) :
    match C.fe.findTable? n with
    | none => C.tblM[n]? = none
    | some tb => ∃ o, C.tblM[n]? = some (ecell C o) ∧ TblE C.EB C.EH o tb := hok.envRel.2 n

theorem tblE_lt {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {tb : IProjTable} (h : TblE EB H o tb) :
    o < H.length := (List.getElem?_eq_some_iff.mp h.1).1

end

section
variable {σ : Type}

theorem rpc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rpcLocals → (ctxEnv C ++ rpcParams.zip vals).get x = none :=
  Knot.params_none C rpcLocals rpcParams vals (by decide) (by decide)

/-- The code `reduceProjCore` calls. -/
structure RpcCodes (C : Ctx) : Prop where
  tc : TcCodes C
  ttc : C.code.lookup fTc = some ([(tcH, ShapeHOL.one)], tcBody C, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  pl : C.code.lookup fPl = some (kParams.map (fun p => (p, ShapeHOL.one)), plBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  pc : C.code.lookup fPc = some (pcParams.map (fun p => (p, ShapeHOL.one)), pcBody C, .one)
  pp : C.code.lookup fPp = some (ppParams.map (fun p => (p, ShapeHOL.one)), ppBody, .one)

theorem rpcCodes_H {C : Ctx} (hc : RpcCodes C) (H : List (BitVec 64)) : RpcCodes (ctxH C H) :=
  ⟨⟨slCodes_H hc.tc.sl H, hc.tc.lit, hc.tc.ls, hc.tc.ic⟩, hc.ttc, hc.w, hc.pl, hc.mg, hc.mp, hc.af, hc.gaa, hc.bv,
    hc.pc, hc.pp⟩

theorem arg_addr (C : Ctx) (o a b : Nat) (ha : a < 2 ^ 59) (hb : b < 2 ^ 59) :
    cellA C o + (BitVec.ofNat 64 a <<< (3 : Nat) + BitVec.ofNat 64 b <<< (3 : Nat) + 8#64) = cellA C (o + 1 + (a + b)) := by
  rw [w_shl a 3 (by omega), w_shl b 3 (by omega), show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, show a * 2 ^ 3 + b * 2 ^ 3 + 8 = 8 * (1 + (a + b)) by omega,
    ExPre.cellA_off, Nat.add_assoc]

theorem rpc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : RpcCodes C) (s : AState) (d : Nat) (sn : NIdx) (i : Nat) (c : EIdx) (hi : i < 2 ^ 64)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (rpcParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i,
      Enc.idxW c])) (rpcBody mode.verifiedChecks C) s (reduceProjCore mode (knot mode C n) C.fe d sn i c)
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (rpc_none C _) ?_
  unfold rpcCore reduceProjCore
  refine specR_callKH rqE fPl kParams [vv kFu, vv kD, vv sP] plBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c] (by decide) rfl (by decide) hc.pl
    ⟨by simp +decide [Env.get, rpcParams, ctxEnv], by simp +decide [Env.get, rpcParams, ctxEnv],
      by simp +decide [Env.get, rpcParams, ctxEnv], trivial⟩
    (pl_spec ra mode n C hok hc.tc hc.ttc hc.w s d c hW) (fun e' s1 H1 hp1 => ?_)
  have hok1 := ctxOK_H hok H1
  have hc1 := rpcCodes_H hc H1
  refine specR_tblFindI (C := ctxH C H1) hok1 hc.mg hc.mp rqT (vv sN) sn (by decide)
    (by simp +decide [Env.get, rpcParams, ctxEnv]) (by simp +decide [Env.get, rpcParams, ctxEnv]; rfl) ?_
  have hrel := tbl_rel hok sn
  unfold IFEnv.findProj?
  revert hrel
  rcases hft : C.fe.findTable? sn with _ | tb
  · intro hrel; simp only at hrel
    rw [show (ctxH C H1).tblM[sn]? = none from hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, htb⟩
  rw [show (ctxH C H1).tblM[sn]? = some (ecell C o) from hm]
  dsimp only
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI rqQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  obtain ⟨_, ⟨wl, hwl, hlps⟩, hnp, hctor, hnf, _⟩ := htb
  refine specR_envLoadI (C := ctxH C H1) rqNf (.op .add [vv rqQ, .const 32]) (o + 4) _ (by decide)
    (by simp [sev, vv]; exact UD.ecell_add32 C o) hnf.1 ?_
  by_cases hin : i < tb.numFields
  · rw [ite_eq_left hin]
    have hlw := word_lt_iff i tb.numFields (by unfold B; omega) (by unfold B; have := hnf.2; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rpcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_callNIM (C := ctxH C H1) rqHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv rqE]
      getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e'] (by decide) rfl (by decide) hc.af
      ⟨rfl, by simp, trivial⟩
      (fun a w s' st => getAppFn coreWalkFuel e' s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
      (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H1) hc.af coreWalkFuel e' s1 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
          hlk 1 (by decide)⟩))
      (fun hh w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s1 = s' := hs.symm
    subst hs'
    have hret0 : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)} {s2 : AState}, H1 <+: H →
        SpecR (σ := σ) (Inv (ctxH C H) s2 Γ M (ctxLocals ++ rpcLocals)) (.return (.const 0)) s2
          (pure none : AM (Option EIdx)) (UD.PostO C) :=
      fun hp => specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨_, hp1.trans hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine Knot.specR_tagIteV rqHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
      exact hret0 (List.prefix_refl _)
    rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv rqHh) (Enc.idxW hh) (by decide) (by simp) ?_
    refine ILP.specR_viewIv hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun v P hv htn _ => ?_)
    have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
    obtain ⟨k, us, rfl⟩ := UD.tagN_const h3
    dsimp only
    refine specR_loadI' rqK (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW k) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW k) [Enc.idxW us] []) ?_
    refine specR_loadI' rqU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW k) (Enc.idxW us) [] []) ?_
    refine specR_dropM ?_
    refine specR_callNIH (C := ctxH C H1) rqA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv rqE]
      (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e'] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp, trivial⟩
      (PostA (ctxH C H1)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
      (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec (ctxH C H1) hok1 hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 e' s1))
      (fun args w s2 H2 hp2 ⟨o3, hw, hb3⟩ => ?_)
    subst hw
    have hok2 := ctxOK_H hok H2
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv rqU) (Enc.idxW us) (by decide) (by simp) ?_
    refine specR_lsviewPI us (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    refine specR_runBind (viewLsLen_run us s2 vl hvl) ?_
    dsimp only
    refine specR_envLoadI (C := ctxH C H2) rqCt (.op .add [vv rqQ, .const 24]) (o + 3) _ (by decide)
      (by simp [sev, vv]; exact ecell_add24 C o) hctor ?_
    refine specR_envLoadI (C := ctxH C H2) rqNp (.op .add [vv rqQ, .const 16]) (o + 2) _ (by decide)
      (by simp [sev, vv]; exact UD.ecell_add16 C o) hnp.1 ?_
    refine specR_envLoadI (C := ctxH C H2) rqLp (.op .add [vv rqQ, .const 8]) (o + 1) _ (by decide)
      (by simp [sev, vv]; exact ecell_add C o 1) hwl ?_
    obtain ⟨ol, hwol, hblk⟩ := hlps
    refine specR_envLoadI (C := ctxH C H2) rqLl (vv rqLp) ol _ (by decide) (by simp [hwol]; rfl) hblk.1 ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) rqAl (vv rqA) o3 _ hb3.1 (by decide) (by simp; rfl) ?_
    refine specR_atEntry fun t2 ht2 => ?_
    have hargs := blk_small0 (C := ctxH C H2) hok2 ht2.sr hb3
    simp only [List.length_map] at hargs
    have hnp2 := hnp.2
    have hnf2 := hnf.2
    have hp12 : H1 <+: H2 := hp2
    by_cases hk : k = tb.ctor
    swap
    · have hne : Enc.idxW k ≠ Enc.idxW tb.ctor := fun e => hk (Enc.idxW_inj e)
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      rw [ite_eq_right (by simp [IProjTable.entry, hk])]
      exact hret0 hp12
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk]) (fun h => absurd rfl h)
      (fun _ => ?_)
    have hweq : (BitVec.ofNat 64 args.length = BitVec.ofNat 64 tb.numParams + BitVec.ofNat 64 tb.numFields) ↔
        args.length = tb.numParams + tb.numFields := by
      rw [BitVec.ofNat_add_ofNat]
      constructor
      · intro e; have := congrArg BitVec.toNat e; simp at this; omega
      · intro e; rw [e]
    by_cases hal : args.length = tb.numParams + tb.numFields
    swap
    · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact fun e => hal (hweq.mp e))
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [ite_eq_right (by simp [IProjTable.entry, hal])]
      exact hret0 hp12
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hweq.mpr hal)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlpl : tb.levelParams.length < 2 ^ 61 := by
      have h1 := blkAt_len (show BlkAt C.EH ol (tb.levelParams.map Enc.idxW) from hblk)
      have h2 := ht2.sr.env.1.len; have h3 := hok.envLay
      simp only [List.length_map] at h1; simp only [ctxH] at h2; omega
    have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
    have hweq2 : (BitVec.ofNat 64 vl.length = BitVec.ofNat 64 tb.levelParams.length) ↔
        vl.length = tb.levelParams.length := by
      constructor
      · intro e; have := congrArg BitVec.toNat e; simp at this; omega
      · intro e; rw [e]
    by_cases hul : vl.length = tb.levelParams.length
    swap
    · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact fun e => hul (hweq2.mp e))
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [ite_eq_right (by simp [IProjTable.entry, hul])]
      exact hret0 hp12
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hweq2.mpr hul)
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [ite_eq_left (by simp [IProjTable.entry, hk, hin, hal, hul])]
    refine specR_internBVarI (C := ctxH C H2) ra hok2 hc.bv rqB0 (.const 0) 0 (by decide) (by decide) rfl
      (fun b0 s3 => ?_)
    have hj : tb.numParams + i < args.length := by omega
    have hgd : args.getD ((tb.entry i).numParams + i) b0 = args[tb.numParams + i] := by
      simp [IProjTable.entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    refine UD.specR_heapLoadI' (C := ctxH C H2) rqX _ (o3 + 1 + (tb.numParams + i)) (Enc.idxW args[tb.numParams + i])
      (by have := hb3.2 (tb.numParams + i) (by simpa using hj); simp only [List.getElem_map] at this; exact this)
      (by decide)
      (by
        simp +decide [sev, Env.get, rpcParams, ctxEnv]
        exact arg_addr C o3 _ _ (by omega) (by omega)) ?_
    try dsimp only
    rw [hgd]
    unfold projCertAt
    cases hvc : mode.verifiedChecks
    · simp only [rpcCert, Bool.false_eq_true, ite_false, pure_bind, ite_true]
      exact specR_returnI _ (optW (some args[tb.numParams + i])) (by simp [sev, vv, optWG])
        (fun t ht => ⟨H2, hp1.trans hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · simp only [rpcCert, ite_true]
      refine specR_callNIH (C := ctxH C H2) rqOk fPc pcParams [vv rqK, vv rqAl] (pcBody C)
        [Enc.idxW k, BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hc.pc
        ⟨by simp, by simp, trivial⟩ (Knot.PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
        (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pcParams _ rfl hlk)
          (pc_spec (ctxH C H2) hok2 hc.mg hc.mp hc.pp k args s3 (by omega)))
        (fun b w s4 H4 hp4 hw => ?_)
      subst hw
      cases b
      · refine specR_ifI _ (boolW false) (by simp) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [Bool.false_eq_true, ite_false]
        exact hret0 (hp12.trans hp4)
      · refine specR_ifI _ (boolW true) (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [ite_true]
        exact specR_returnI _ (optW (some args[tb.numParams + i])) (by simp [sev, vv, optWG])
          (fun t ht => ⟨H4, hp1.trans (hp12.trans hp4), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [ite_eq_right hin]
    have hlw := word_lt_iff i tb.numFields (by unfold B; omega) (by unfold B; have := hnf.2; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rpcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; have := hnf.2; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
