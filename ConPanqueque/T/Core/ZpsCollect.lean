import ConPanqueque.T.Core.ZeSubst
import ConPanqueque.T.Ex.AppendFn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `zps` collected into a block

`zc(u, acc)`: the block `acc ++ ns`, `ns` the parameter-name handles of the zero-ness datum of the level `u`
(`zps`, in order). Appends go through fresh blocks (`appendWord`). Read-only otherwise.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def zcU := ofString "zpc_zcu"
def zcA := ofString "zpc_zca"
def zcN := ofString "zpc_zcn"
def zcX := ofString "zpc_zcx"
def zcY := ofString "zpc_zcy"
def zcR1 := ofString "zpc_zcr1"
def zcR := ofString "zpc_zcr"
def fZc := ofString "zpsCollect"

@[simp] theorem zpc_zcU_ne_zcA : zcU ≠ zcA := by decide
@[simp] theorem zpc_zcU_ne_zcN : zcU ≠ zcN := by decide
@[simp] theorem zpc_zcU_ne_zcX : zcU ≠ zcX := by decide
@[simp] theorem zpc_zcU_ne_zcY : zcU ≠ zcY := by decide
@[simp] theorem zpc_zcU_ne_zcR1 : zcU ≠ zcR1 := by decide
@[simp] theorem zpc_zcU_ne_zcR : zcU ≠ zcR := by decide
@[simp] theorem zpc_zcU_ne_lFl : zcU ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcU : lFl ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lDh : zcU ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcU : lDh ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lDt : zcU ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcU : lDt ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lDg : zcU ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcU : lDg ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lDi : zcU ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcU : lDi ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lRp : zcU ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcU : lRp ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lRn : zcU ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcU : lRn ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lFle : zcU ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcU : lFle ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lKb : zcU ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcU : lKb ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lDir : zcU ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcU : lDir ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lFln : zcU ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcU : lFln ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lFll : zcU ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcU : lFll ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_lFls : zcU ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcU : lFls ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_kFu : zcU ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcU : kFu ≠ zcU := by decide
@[simp] theorem zpc_zcU_ne_kD : zcU ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcU : kD ≠ zcU := by decide
@[simp] theorem zpc_zcA_ne_zcU : zcA ≠ zcU := by decide
@[simp] theorem zpc_zcA_ne_zcN : zcA ≠ zcN := by decide
@[simp] theorem zpc_zcA_ne_zcX : zcA ≠ zcX := by decide
@[simp] theorem zpc_zcA_ne_zcY : zcA ≠ zcY := by decide
@[simp] theorem zpc_zcA_ne_zcR1 : zcA ≠ zcR1 := by decide
@[simp] theorem zpc_zcA_ne_zcR : zcA ≠ zcR := by decide
@[simp] theorem zpc_zcA_ne_lFl : zcA ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcA : lFl ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lDh : zcA ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcA : lDh ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lDt : zcA ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcA : lDt ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lDg : zcA ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcA : lDg ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lDi : zcA ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcA : lDi ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lRp : zcA ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcA : lRp ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lRn : zcA ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcA : lRn ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lFle : zcA ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcA : lFle ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lKb : zcA ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcA : lKb ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lDir : zcA ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcA : lDir ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lFln : zcA ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcA : lFln ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lFll : zcA ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcA : lFll ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_lFls : zcA ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcA : lFls ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_kFu : zcA ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcA : kFu ≠ zcA := by decide
@[simp] theorem zpc_zcA_ne_kD : zcA ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcA : kD ≠ zcA := by decide
@[simp] theorem zpc_zcN_ne_zcU : zcN ≠ zcU := by decide
@[simp] theorem zpc_zcN_ne_zcA : zcN ≠ zcA := by decide
@[simp] theorem zpc_zcN_ne_zcX : zcN ≠ zcX := by decide
@[simp] theorem zpc_zcN_ne_zcY : zcN ≠ zcY := by decide
@[simp] theorem zpc_zcN_ne_zcR1 : zcN ≠ zcR1 := by decide
@[simp] theorem zpc_zcN_ne_zcR : zcN ≠ zcR := by decide
@[simp] theorem zpc_zcN_ne_lFl : zcN ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcN : lFl ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lDh : zcN ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcN : lDh ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lDt : zcN ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcN : lDt ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lDg : zcN ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcN : lDg ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lDi : zcN ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcN : lDi ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lRp : zcN ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcN : lRp ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lRn : zcN ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcN : lRn ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lFle : zcN ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcN : lFle ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lKb : zcN ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcN : lKb ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lDir : zcN ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcN : lDir ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lFln : zcN ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcN : lFln ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lFll : zcN ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcN : lFll ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_lFls : zcN ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcN : lFls ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_kFu : zcN ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcN : kFu ≠ zcN := by decide
@[simp] theorem zpc_zcN_ne_kD : zcN ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcN : kD ≠ zcN := by decide
@[simp] theorem zpc_zcX_ne_zcU : zcX ≠ zcU := by decide
@[simp] theorem zpc_zcX_ne_zcA : zcX ≠ zcA := by decide
@[simp] theorem zpc_zcX_ne_zcN : zcX ≠ zcN := by decide
@[simp] theorem zpc_zcX_ne_zcY : zcX ≠ zcY := by decide
@[simp] theorem zpc_zcX_ne_zcR1 : zcX ≠ zcR1 := by decide
@[simp] theorem zpc_zcX_ne_zcR : zcX ≠ zcR := by decide
@[simp] theorem zpc_zcX_ne_lFl : zcX ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcX : lFl ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lDh : zcX ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcX : lDh ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lDt : zcX ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcX : lDt ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lDg : zcX ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcX : lDg ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lDi : zcX ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcX : lDi ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lRp : zcX ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcX : lRp ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lRn : zcX ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcX : lRn ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lFle : zcX ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcX : lFle ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lKb : zcX ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcX : lKb ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lDir : zcX ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcX : lDir ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lFln : zcX ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcX : lFln ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lFll : zcX ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcX : lFll ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_lFls : zcX ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcX : lFls ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_kFu : zcX ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcX : kFu ≠ zcX := by decide
@[simp] theorem zpc_zcX_ne_kD : zcX ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcX : kD ≠ zcX := by decide
@[simp] theorem zpc_zcY_ne_zcU : zcY ≠ zcU := by decide
@[simp] theorem zpc_zcY_ne_zcA : zcY ≠ zcA := by decide
@[simp] theorem zpc_zcY_ne_zcN : zcY ≠ zcN := by decide
@[simp] theorem zpc_zcY_ne_zcX : zcY ≠ zcX := by decide
@[simp] theorem zpc_zcY_ne_zcR1 : zcY ≠ zcR1 := by decide
@[simp] theorem zpc_zcY_ne_zcR : zcY ≠ zcR := by decide
@[simp] theorem zpc_zcY_ne_lFl : zcY ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcY : lFl ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lDh : zcY ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcY : lDh ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lDt : zcY ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcY : lDt ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lDg : zcY ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcY : lDg ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lDi : zcY ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcY : lDi ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lRp : zcY ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcY : lRp ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lRn : zcY ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcY : lRn ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lFle : zcY ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcY : lFle ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lKb : zcY ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcY : lKb ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lDir : zcY ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcY : lDir ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lFln : zcY ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcY : lFln ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lFll : zcY ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcY : lFll ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_lFls : zcY ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcY : lFls ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_kFu : zcY ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcY : kFu ≠ zcY := by decide
@[simp] theorem zpc_zcY_ne_kD : zcY ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcY : kD ≠ zcY := by decide
@[simp] theorem zpc_zcR1_ne_zcU : zcR1 ≠ zcU := by decide
@[simp] theorem zpc_zcR1_ne_zcA : zcR1 ≠ zcA := by decide
@[simp] theorem zpc_zcR1_ne_zcN : zcR1 ≠ zcN := by decide
@[simp] theorem zpc_zcR1_ne_zcX : zcR1 ≠ zcX := by decide
@[simp] theorem zpc_zcR1_ne_zcY : zcR1 ≠ zcY := by decide
@[simp] theorem zpc_zcR1_ne_zcR : zcR1 ≠ zcR := by decide
@[simp] theorem zpc_zcR1_ne_lFl : zcR1 ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcR1 : lFl ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lDh : zcR1 ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcR1 : lDh ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lDt : zcR1 ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcR1 : lDt ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lDg : zcR1 ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcR1 : lDg ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lDi : zcR1 ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcR1 : lDi ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lRp : zcR1 ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcR1 : lRp ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lRn : zcR1 ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcR1 : lRn ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lFle : zcR1 ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcR1 : lFle ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lKb : zcR1 ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcR1 : lKb ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lDir : zcR1 ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcR1 : lDir ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lFln : zcR1 ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcR1 : lFln ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lFll : zcR1 ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcR1 : lFll ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_lFls : zcR1 ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcR1 : lFls ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_kFu : zcR1 ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcR1 : kFu ≠ zcR1 := by decide
@[simp] theorem zpc_zcR1_ne_kD : zcR1 ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcR1 : kD ≠ zcR1 := by decide
@[simp] theorem zpc_zcR_ne_zcU : zcR ≠ zcU := by decide
@[simp] theorem zpc_zcR_ne_zcA : zcR ≠ zcA := by decide
@[simp] theorem zpc_zcR_ne_zcN : zcR ≠ zcN := by decide
@[simp] theorem zpc_zcR_ne_zcX : zcR ≠ zcX := by decide
@[simp] theorem zpc_zcR_ne_zcY : zcR ≠ zcY := by decide
@[simp] theorem zpc_zcR_ne_zcR1 : zcR ≠ zcR1 := by decide
@[simp] theorem zpc_zcR_ne_lFl : zcR ≠ lFl := by decide
@[simp] theorem zpc_lFl_ne_zcR : lFl ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lDh : zcR ≠ lDh := by decide
@[simp] theorem zpc_lDh_ne_zcR : lDh ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lDt : zcR ≠ lDt := by decide
@[simp] theorem zpc_lDt_ne_zcR : lDt ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lDg : zcR ≠ lDg := by decide
@[simp] theorem zpc_lDg_ne_zcR : lDg ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lDi : zcR ≠ lDi := by decide
@[simp] theorem zpc_lDi_ne_zcR : lDi ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lRp : zcR ≠ lRp := by decide
@[simp] theorem zpc_lRp_ne_zcR : lRp ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lRn : zcR ≠ lRn := by decide
@[simp] theorem zpc_lRn_ne_zcR : lRn ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lFle : zcR ≠ lFle := by decide
@[simp] theorem zpc_lFle_ne_zcR : lFle ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lKb : zcR ≠ lKb := by decide
@[simp] theorem zpc_lKb_ne_zcR : lKb ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lDir : zcR ≠ lDir := by decide
@[simp] theorem zpc_lDir_ne_zcR : lDir ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lFln : zcR ≠ lFln := by decide
@[simp] theorem zpc_lFln_ne_zcR : lFln ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lFll : zcR ≠ lFll := by decide
@[simp] theorem zpc_lFll_ne_zcR : lFll ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_lFls : zcR ≠ lFls := by decide
@[simp] theorem zpc_lFls_ne_zcR : lFls ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_kFu : zcR ≠ kFu := by decide
@[simp] theorem zpc_kFu_ne_zcR : kFu ≠ zcR := by decide
@[simp] theorem zpc_zcR_ne_kD : zcR ≠ kD := by decide
@[simp] theorem zpc_kD_ne_zcR : kD ≠ zcR := by decide

def zcParams : List MlS := [zcU, zcA]
def zcLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zcN, zcX, zcY, zcR1, zcR]
def zcBody : ProgHOL 64 := prologue zcLocals (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zcU)) (.seq lViewP (.ite (.cmp .equal (vv lDg) (.const 4)) (.seq (.assign .local zcN (.load .one (vv lRp))) (.seq (.call (some (some (.local, zcR), none)) ExPre.fAppend [(vv zcA), (vv zcN)]) (.return (vv zcR)))) (.ite (.cmp .equal (vv lDg) (.const 2)) (.seq (.assign .local zcX (.load .one (vv lRp))) (.seq (.assign .local zcY (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, zcR1), none)) fZc [(vv zcX), (vv zcA)]) (.seq (.call (some (some (.local, zcR), none)) fZc [(vv zcY), (vv zcR1)]) (.return (vv zcR)))))) (.ite (.cmp .equal (vv lDg) (.const 3)) (.seq (.assign .local zcY (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, zcR), none)) fZc [(vv zcY), (vv zcA)]) (.return (vv zcR)))) (.return (vv zcA))))))))

structure ZcCodes (C : Ctx) : Prop where
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fZc = some (zcParams.map (fun p => (p, ShapeHOL.one)), zcBody, .one)

theorem dnl_append {st : NStore} : ∀ {xs ys : List NIdx} {a b : List Name},
    Frontend.denoteNList st xs = some a → Frontend.denoteNList st ys = some b →
    Frontend.denoteNList st (xs ++ ys) = some (a ++ b) := by
  intro xs
  induction xs with
  | nil => intro ys a b ha hb; simp [Frontend.denoteNList] at ha; subst ha; simpa using hb
  | cons x xs ih =>
    intro ys a b ha hb
    rw [List.cons_append]
    unfold Frontend.denoteNList at ha ⊢
    cases hx : denoteN st x <;> cases hxs : Frontend.denoteNList st xs <;> simp [hx, hxs] at ha
    subst ha
    simp [ih hxs hb]

section
variable {σ : Type}

def PostZc (C : Ctx) (s : AState) (acc : List NIdx) (r : List Name) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o ns, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o ((acc ++ ns).map Enc.idxW) ∧
    Frontend.denoteNList s.store.ls.ns ns = some r ∧ SR (ctxH C H') s st

theorem postZc_locals (C : Ctx) (s : AState) (acc : List NIdx) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostZc C s acc a w s' st → PostZc C s acc a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, ns, h2, h3, h4, h5, h6⟩ => ⟨h1, H', o, ns, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩

theorem zc_spec (C : Ctx) (hok : CtxOK C) (hc : ZcCodes C) (s : AState) (hwf : LStoreWF s.store.ls) :
    ∀ (l : Level) (u : LIdx) (H : List (BitVec 64)) (acc : List NIdx) (oa : Nat), C.H <+: H →
      denoteL s.store.ls u = some l → BlkAt H oa (acc.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (zcParams.zip [Enc.idxW u, cellA C oa])) zcBody s (pure (zps l) : AM (List Name))
        (PostZc (ctxH C H) s acc) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u H acc oa hpH hd hb
    refine specR_prologue (postZc_locals _ s acc) (Knot.params_none _ zcLocals zcParams _ (by decide) (by decide)) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv zcU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, zcParams, ctxEnv]) ?_
    refine specR_lviewPI (C := ctxH C H) u (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, zcParams, ctxEnv]) (fun t ht => ⟨rfl, H, oa, [], List.prefix_refl _, rfl, by simpa using hb, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)

  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, zcParams, ctxEnv]) (fun t ht => ⟨rfl, H, oa, [], List.prefix_refl _, rfl, by simpa using hb, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)

  -- max
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 2
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' zcX (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zcY _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) zcR1 fZc zcParams [vv zcX, vv zcA] zcBody [Enc.idxW a, cellA C oa] (zps _) (by decide) rfl (by decide) hc.self
        ⟨by simp, by simp <;> rfl, trivial⟩ (PostZc (ctxH C H) s (acc))
        (fun r w _ H' => ∃ o ns, w = cellA C o ∧ BlkAt H' o (((acc) ++ ns).map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some r)
        (fun r w s' st ⟨hs, H', o, ns, hp, hw, hb, hdn, hsr⟩ => ⟨H', hp, ⟨o, ns, hw, hb, hdn⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zcParams _ rfl hlk) (ihp _ H _ _ hpH hda hb))

        (fun w H1 hp1 ⟨o1, ns1, hw, hb1, hdn1⟩ => ?_)
      subst hw
      refine specR_callPure (C := ctxH C H1) zcR fZc zcParams [vv zcY, vv zcR1] zcBody [Enc.idxW b, cellA C o1] (zps _) (by decide) rfl (by decide) hc.self
        ⟨by simp, by simp <;> rfl, trivial⟩ (PostZc (ctxH C H1) s (acc ++ ns1))
        (fun r w _ H' => ∃ o ns, w = cellA C o ∧ BlkAt H' o (((acc ++ ns1) ++ ns).map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some r)
        (fun r w s' st ⟨hs, H', o, ns, hp, hw, hb, hdn, hsr⟩ => ⟨H', hp, ⟨o, ns, hw, hb, hdn⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zcParams _ rfl hlk) (ihq _ H1 _ _ (hpH.trans hp1) hdb (by simpa using hb1)))

        (fun w H2 hp2 ⟨o2, ns2, hw, hb2, hdn2⟩ => ?_)
      subst hw
      exact specR_returnI _ (cellA C o2) (by simp <;> rfl) (fun t ht => ⟨rfl, H2, o2, ns1 ++ ns2, hp1.trans hp2, rfl,
        by simpa [List.append_assoc] using hb2, dnl_append hdn1 hdn2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)

  -- imax
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 3
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' zcY _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) zcR fZc zcParams [vv zcY, vv zcA] zcBody [Enc.idxW b, cellA C oa] (zps _) (by decide) rfl (by decide) hc.self
        ⟨by simp, by simp <;> rfl, trivial⟩ (PostZc (ctxH C H) s (acc))
        (fun r w _ H' => ∃ o ns, w = cellA C o ∧ BlkAt H' o (((acc) ++ ns).map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some r)
        (fun r w s' st ⟨hs, H', o, ns, hp, hw, hb, hdn, hsr⟩ => ⟨H', hp, ⟨o, ns, hw, hb, hdn⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zcParams _ rfl hlk) (ihq _ H _ _ hpH hdb hb))

        (fun w H1 hp1 ⟨o1, ns1, hw, hb1, hdn1⟩ => ?_)
      subst hw
      exact specR_returnI _ (cellA C o1) (by simp <;> rfl) (fun t ht => ⟨rfl, H1, o1, ns1, hp1, rfl, hb1, hdn1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)

  -- param
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 4
    · obtain ⟨nm', he, hdn⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd
      cases he
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' zcN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_dropM ?_
      refine ExPre.specR_callApp (C := ctxH C H) (ctxOK_H hok H) hc.app zcR (vv zcA) (vv zcN) oa (acc.map Enc.idxW) (Enc.idxW n)
        (by decide) hb (by simp <;> rfl) (by simp) (fun H1 o1 hp1 hb1 => ?_)
      exact specR_returnI _ (cellA C o1) (by simp <;> rfl) (fun t ht => ⟨rfl, H1, o1, [n], hp1, rfl, by simpa using hb1,
        by simp [Frontend.denoteNList, hdn, zps], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)

end

end ConPanqueque.T.WC
