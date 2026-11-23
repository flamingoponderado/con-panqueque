import ConPanqueque.T.Core.CheckProjGuard
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `IProjEntry.typeAt`

The projected field's stored type (the table's `bodies[i]`, at the table's level parameters copied to the heap)
at the use's levels (`instLPFast`), then opened at the structure's arguments and the subject
(`targs ++ [pe]`, one `instantiateListFast`). An index outside the bodies block halts.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)

def taT := ofString "tan_t"
def taI := ofString "tan_i"
def taUs := ofString "tan_us"
def taVa := ofString "tan_va"
def taPe := ofString "tan_pe"
def taLp := ofString "tan_lp"
def taLl := ofString "tan_ll"
def taB := ofString "tan_b"
def taBd := ofString "tan_bd"
def taBn := ofString "tan_bn"
def taE := ofString "tan_e"
def taY := ofString "tan_y"
def taA := ofString "tan_a"
def taL := ofString "tan_l"
def taR := ofString "tan_r"
def fTa := ofString "typeAt"

@[simp] theorem ta_taT_ne_taI : taT ≠ taI := by decide
@[simp] theorem ta_taT_ne_taUs : taT ≠ taUs := by decide
@[simp] theorem ta_taT_ne_taVa : taT ≠ taVa := by decide
@[simp] theorem ta_taT_ne_taPe : taT ≠ taPe := by decide
@[simp] theorem ta_taT_ne_taLp : taT ≠ taLp := by decide
@[simp] theorem ta_taT_ne_taLl : taT ≠ taLl := by decide
@[simp] theorem ta_taT_ne_taB : taT ≠ taB := by decide
@[simp] theorem ta_taT_ne_taBd : taT ≠ taBd := by decide
@[simp] theorem ta_taT_ne_taBn : taT ≠ taBn := by decide
@[simp] theorem ta_taT_ne_taE : taT ≠ taE := by decide
@[simp] theorem ta_taT_ne_taY : taT ≠ taY := by decide
@[simp] theorem ta_taT_ne_taA : taT ≠ taA := by decide
@[simp] theorem ta_taT_ne_taL : taT ≠ taL := by decide
@[simp] theorem ta_taT_ne_taR : taT ≠ taR := by decide
@[simp] theorem ta_taT_ne_lFl : taT ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taT : lFl ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDh : taT ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taT : lDh ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDt : taT ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taT : lDt ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDg : taT ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taT : lDg ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDi : taT ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taT : lDi ≠ taT := by decide
@[simp] theorem ta_taT_ne_lRp : taT ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taT : lRp ≠ taT := by decide
@[simp] theorem ta_taT_ne_lRn : taT ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taT : lRn ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDir : taT ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taT : lDir ≠ taT := by decide
@[simp] theorem ta_taT_ne_lFle : taT ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taT : lFle ≠ taT := by decide
@[simp] theorem ta_taT_ne_lKb : taT ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taT : lKb ≠ taT := by decide
@[simp] theorem ta_taT_ne_lCn : taT ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taT : lCn ≠ taT := by decide
@[simp] theorem ta_taT_ne_lSrc : taT ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taT : lSrc ≠ taT := by decide
@[simp] theorem ta_taT_ne_lDst : taT ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taT : lDst ≠ taT := by decide
@[simp] theorem ta_taT_ne_lCi : taT ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taT : lCi ≠ taT := by decide
@[simp] theorem ta_taT_ne_lCz : taT ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taT : lCz ≠ taT := by decide
@[simp] theorem ta_taI_ne_taT : taI ≠ taT := by decide
@[simp] theorem ta_taI_ne_taUs : taI ≠ taUs := by decide
@[simp] theorem ta_taI_ne_taVa : taI ≠ taVa := by decide
@[simp] theorem ta_taI_ne_taPe : taI ≠ taPe := by decide
@[simp] theorem ta_taI_ne_taLp : taI ≠ taLp := by decide
@[simp] theorem ta_taI_ne_taLl : taI ≠ taLl := by decide
@[simp] theorem ta_taI_ne_taB : taI ≠ taB := by decide
@[simp] theorem ta_taI_ne_taBd : taI ≠ taBd := by decide
@[simp] theorem ta_taI_ne_taBn : taI ≠ taBn := by decide
@[simp] theorem ta_taI_ne_taE : taI ≠ taE := by decide
@[simp] theorem ta_taI_ne_taY : taI ≠ taY := by decide
@[simp] theorem ta_taI_ne_taA : taI ≠ taA := by decide
@[simp] theorem ta_taI_ne_taL : taI ≠ taL := by decide
@[simp] theorem ta_taI_ne_taR : taI ≠ taR := by decide
@[simp] theorem ta_taI_ne_lFl : taI ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taI : lFl ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDh : taI ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taI : lDh ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDt : taI ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taI : lDt ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDg : taI ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taI : lDg ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDi : taI ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taI : lDi ≠ taI := by decide
@[simp] theorem ta_taI_ne_lRp : taI ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taI : lRp ≠ taI := by decide
@[simp] theorem ta_taI_ne_lRn : taI ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taI : lRn ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDir : taI ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taI : lDir ≠ taI := by decide
@[simp] theorem ta_taI_ne_lFle : taI ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taI : lFle ≠ taI := by decide
@[simp] theorem ta_taI_ne_lKb : taI ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taI : lKb ≠ taI := by decide
@[simp] theorem ta_taI_ne_lCn : taI ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taI : lCn ≠ taI := by decide
@[simp] theorem ta_taI_ne_lSrc : taI ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taI : lSrc ≠ taI := by decide
@[simp] theorem ta_taI_ne_lDst : taI ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taI : lDst ≠ taI := by decide
@[simp] theorem ta_taI_ne_lCi : taI ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taI : lCi ≠ taI := by decide
@[simp] theorem ta_taI_ne_lCz : taI ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taI : lCz ≠ taI := by decide
@[simp] theorem ta_taUs_ne_taT : taUs ≠ taT := by decide
@[simp] theorem ta_taUs_ne_taI : taUs ≠ taI := by decide
@[simp] theorem ta_taUs_ne_taVa : taUs ≠ taVa := by decide
@[simp] theorem ta_taUs_ne_taPe : taUs ≠ taPe := by decide
@[simp] theorem ta_taUs_ne_taLp : taUs ≠ taLp := by decide
@[simp] theorem ta_taUs_ne_taLl : taUs ≠ taLl := by decide
@[simp] theorem ta_taUs_ne_taB : taUs ≠ taB := by decide
@[simp] theorem ta_taUs_ne_taBd : taUs ≠ taBd := by decide
@[simp] theorem ta_taUs_ne_taBn : taUs ≠ taBn := by decide
@[simp] theorem ta_taUs_ne_taE : taUs ≠ taE := by decide
@[simp] theorem ta_taUs_ne_taY : taUs ≠ taY := by decide
@[simp] theorem ta_taUs_ne_taA : taUs ≠ taA := by decide
@[simp] theorem ta_taUs_ne_taL : taUs ≠ taL := by decide
@[simp] theorem ta_taUs_ne_taR : taUs ≠ taR := by decide
@[simp] theorem ta_taUs_ne_lFl : taUs ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taUs : lFl ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDh : taUs ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taUs : lDh ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDt : taUs ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taUs : lDt ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDg : taUs ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taUs : lDg ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDi : taUs ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taUs : lDi ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lRp : taUs ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taUs : lRp ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lRn : taUs ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taUs : lRn ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDir : taUs ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taUs : lDir ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lFle : taUs ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taUs : lFle ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lKb : taUs ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taUs : lKb ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lCn : taUs ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taUs : lCn ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lSrc : taUs ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taUs : lSrc ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lDst : taUs ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taUs : lDst ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lCi : taUs ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taUs : lCi ≠ taUs := by decide
@[simp] theorem ta_taUs_ne_lCz : taUs ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taUs : lCz ≠ taUs := by decide
@[simp] theorem ta_taVa_ne_taT : taVa ≠ taT := by decide
@[simp] theorem ta_taVa_ne_taI : taVa ≠ taI := by decide
@[simp] theorem ta_taVa_ne_taUs : taVa ≠ taUs := by decide
@[simp] theorem ta_taVa_ne_taPe : taVa ≠ taPe := by decide
@[simp] theorem ta_taVa_ne_taLp : taVa ≠ taLp := by decide
@[simp] theorem ta_taVa_ne_taLl : taVa ≠ taLl := by decide
@[simp] theorem ta_taVa_ne_taB : taVa ≠ taB := by decide
@[simp] theorem ta_taVa_ne_taBd : taVa ≠ taBd := by decide
@[simp] theorem ta_taVa_ne_taBn : taVa ≠ taBn := by decide
@[simp] theorem ta_taVa_ne_taE : taVa ≠ taE := by decide
@[simp] theorem ta_taVa_ne_taY : taVa ≠ taY := by decide
@[simp] theorem ta_taVa_ne_taA : taVa ≠ taA := by decide
@[simp] theorem ta_taVa_ne_taL : taVa ≠ taL := by decide
@[simp] theorem ta_taVa_ne_taR : taVa ≠ taR := by decide
@[simp] theorem ta_taVa_ne_lFl : taVa ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taVa : lFl ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDh : taVa ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taVa : lDh ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDt : taVa ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taVa : lDt ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDg : taVa ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taVa : lDg ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDi : taVa ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taVa : lDi ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lRp : taVa ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taVa : lRp ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lRn : taVa ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taVa : lRn ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDir : taVa ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taVa : lDir ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lFle : taVa ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taVa : lFle ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lKb : taVa ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taVa : lKb ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lCn : taVa ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taVa : lCn ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lSrc : taVa ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taVa : lSrc ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lDst : taVa ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taVa : lDst ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lCi : taVa ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taVa : lCi ≠ taVa := by decide
@[simp] theorem ta_taVa_ne_lCz : taVa ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taVa : lCz ≠ taVa := by decide
@[simp] theorem ta_taPe_ne_taT : taPe ≠ taT := by decide
@[simp] theorem ta_taPe_ne_taI : taPe ≠ taI := by decide
@[simp] theorem ta_taPe_ne_taUs : taPe ≠ taUs := by decide
@[simp] theorem ta_taPe_ne_taVa : taPe ≠ taVa := by decide
@[simp] theorem ta_taPe_ne_taLp : taPe ≠ taLp := by decide
@[simp] theorem ta_taPe_ne_taLl : taPe ≠ taLl := by decide
@[simp] theorem ta_taPe_ne_taB : taPe ≠ taB := by decide
@[simp] theorem ta_taPe_ne_taBd : taPe ≠ taBd := by decide
@[simp] theorem ta_taPe_ne_taBn : taPe ≠ taBn := by decide
@[simp] theorem ta_taPe_ne_taE : taPe ≠ taE := by decide
@[simp] theorem ta_taPe_ne_taY : taPe ≠ taY := by decide
@[simp] theorem ta_taPe_ne_taA : taPe ≠ taA := by decide
@[simp] theorem ta_taPe_ne_taL : taPe ≠ taL := by decide
@[simp] theorem ta_taPe_ne_taR : taPe ≠ taR := by decide
@[simp] theorem ta_taPe_ne_lFl : taPe ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taPe : lFl ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDh : taPe ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taPe : lDh ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDt : taPe ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taPe : lDt ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDg : taPe ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taPe : lDg ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDi : taPe ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taPe : lDi ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lRp : taPe ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taPe : lRp ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lRn : taPe ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taPe : lRn ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDir : taPe ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taPe : lDir ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lFle : taPe ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taPe : lFle ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lKb : taPe ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taPe : lKb ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lCn : taPe ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taPe : lCn ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lSrc : taPe ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taPe : lSrc ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lDst : taPe ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taPe : lDst ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lCi : taPe ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taPe : lCi ≠ taPe := by decide
@[simp] theorem ta_taPe_ne_lCz : taPe ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taPe : lCz ≠ taPe := by decide
@[simp] theorem ta_taLp_ne_taT : taLp ≠ taT := by decide
@[simp] theorem ta_taLp_ne_taI : taLp ≠ taI := by decide
@[simp] theorem ta_taLp_ne_taUs : taLp ≠ taUs := by decide
@[simp] theorem ta_taLp_ne_taVa : taLp ≠ taVa := by decide
@[simp] theorem ta_taLp_ne_taPe : taLp ≠ taPe := by decide
@[simp] theorem ta_taLp_ne_taLl : taLp ≠ taLl := by decide
@[simp] theorem ta_taLp_ne_taB : taLp ≠ taB := by decide
@[simp] theorem ta_taLp_ne_taBd : taLp ≠ taBd := by decide
@[simp] theorem ta_taLp_ne_taBn : taLp ≠ taBn := by decide
@[simp] theorem ta_taLp_ne_taE : taLp ≠ taE := by decide
@[simp] theorem ta_taLp_ne_taY : taLp ≠ taY := by decide
@[simp] theorem ta_taLp_ne_taA : taLp ≠ taA := by decide
@[simp] theorem ta_taLp_ne_taL : taLp ≠ taL := by decide
@[simp] theorem ta_taLp_ne_taR : taLp ≠ taR := by decide
@[simp] theorem ta_taLp_ne_lFl : taLp ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taLp : lFl ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDh : taLp ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taLp : lDh ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDt : taLp ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taLp : lDt ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDg : taLp ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taLp : lDg ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDi : taLp ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taLp : lDi ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lRp : taLp ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taLp : lRp ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lRn : taLp ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taLp : lRn ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDir : taLp ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taLp : lDir ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lFle : taLp ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taLp : lFle ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lKb : taLp ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taLp : lKb ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lCn : taLp ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taLp : lCn ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lSrc : taLp ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taLp : lSrc ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lDst : taLp ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taLp : lDst ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lCi : taLp ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taLp : lCi ≠ taLp := by decide
@[simp] theorem ta_taLp_ne_lCz : taLp ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taLp : lCz ≠ taLp := by decide
@[simp] theorem ta_taLl_ne_taT : taLl ≠ taT := by decide
@[simp] theorem ta_taLl_ne_taI : taLl ≠ taI := by decide
@[simp] theorem ta_taLl_ne_taUs : taLl ≠ taUs := by decide
@[simp] theorem ta_taLl_ne_taVa : taLl ≠ taVa := by decide
@[simp] theorem ta_taLl_ne_taPe : taLl ≠ taPe := by decide
@[simp] theorem ta_taLl_ne_taLp : taLl ≠ taLp := by decide
@[simp] theorem ta_taLl_ne_taB : taLl ≠ taB := by decide
@[simp] theorem ta_taLl_ne_taBd : taLl ≠ taBd := by decide
@[simp] theorem ta_taLl_ne_taBn : taLl ≠ taBn := by decide
@[simp] theorem ta_taLl_ne_taE : taLl ≠ taE := by decide
@[simp] theorem ta_taLl_ne_taY : taLl ≠ taY := by decide
@[simp] theorem ta_taLl_ne_taA : taLl ≠ taA := by decide
@[simp] theorem ta_taLl_ne_taL : taLl ≠ taL := by decide
@[simp] theorem ta_taLl_ne_taR : taLl ≠ taR := by decide
@[simp] theorem ta_taLl_ne_lFl : taLl ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taLl : lFl ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDh : taLl ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taLl : lDh ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDt : taLl ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taLl : lDt ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDg : taLl ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taLl : lDg ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDi : taLl ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taLl : lDi ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lRp : taLl ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taLl : lRp ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lRn : taLl ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taLl : lRn ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDir : taLl ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taLl : lDir ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lFle : taLl ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taLl : lFle ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lKb : taLl ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taLl : lKb ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lCn : taLl ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taLl : lCn ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lSrc : taLl ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taLl : lSrc ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lDst : taLl ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taLl : lDst ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lCi : taLl ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taLl : lCi ≠ taLl := by decide
@[simp] theorem ta_taLl_ne_lCz : taLl ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taLl : lCz ≠ taLl := by decide
@[simp] theorem ta_taB_ne_taT : taB ≠ taT := by decide
@[simp] theorem ta_taB_ne_taI : taB ≠ taI := by decide
@[simp] theorem ta_taB_ne_taUs : taB ≠ taUs := by decide
@[simp] theorem ta_taB_ne_taVa : taB ≠ taVa := by decide
@[simp] theorem ta_taB_ne_taPe : taB ≠ taPe := by decide
@[simp] theorem ta_taB_ne_taLp : taB ≠ taLp := by decide
@[simp] theorem ta_taB_ne_taLl : taB ≠ taLl := by decide
@[simp] theorem ta_taB_ne_taBd : taB ≠ taBd := by decide
@[simp] theorem ta_taB_ne_taBn : taB ≠ taBn := by decide
@[simp] theorem ta_taB_ne_taE : taB ≠ taE := by decide
@[simp] theorem ta_taB_ne_taY : taB ≠ taY := by decide
@[simp] theorem ta_taB_ne_taA : taB ≠ taA := by decide
@[simp] theorem ta_taB_ne_taL : taB ≠ taL := by decide
@[simp] theorem ta_taB_ne_taR : taB ≠ taR := by decide
@[simp] theorem ta_taB_ne_lFl : taB ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taB : lFl ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDh : taB ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taB : lDh ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDt : taB ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taB : lDt ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDg : taB ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taB : lDg ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDi : taB ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taB : lDi ≠ taB := by decide
@[simp] theorem ta_taB_ne_lRp : taB ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taB : lRp ≠ taB := by decide
@[simp] theorem ta_taB_ne_lRn : taB ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taB : lRn ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDir : taB ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taB : lDir ≠ taB := by decide
@[simp] theorem ta_taB_ne_lFle : taB ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taB : lFle ≠ taB := by decide
@[simp] theorem ta_taB_ne_lKb : taB ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taB : lKb ≠ taB := by decide
@[simp] theorem ta_taB_ne_lCn : taB ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taB : lCn ≠ taB := by decide
@[simp] theorem ta_taB_ne_lSrc : taB ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taB : lSrc ≠ taB := by decide
@[simp] theorem ta_taB_ne_lDst : taB ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taB : lDst ≠ taB := by decide
@[simp] theorem ta_taB_ne_lCi : taB ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taB : lCi ≠ taB := by decide
@[simp] theorem ta_taB_ne_lCz : taB ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taB : lCz ≠ taB := by decide
@[simp] theorem ta_taBd_ne_taT : taBd ≠ taT := by decide
@[simp] theorem ta_taBd_ne_taI : taBd ≠ taI := by decide
@[simp] theorem ta_taBd_ne_taUs : taBd ≠ taUs := by decide
@[simp] theorem ta_taBd_ne_taVa : taBd ≠ taVa := by decide
@[simp] theorem ta_taBd_ne_taPe : taBd ≠ taPe := by decide
@[simp] theorem ta_taBd_ne_taLp : taBd ≠ taLp := by decide
@[simp] theorem ta_taBd_ne_taLl : taBd ≠ taLl := by decide
@[simp] theorem ta_taBd_ne_taB : taBd ≠ taB := by decide
@[simp] theorem ta_taBd_ne_taBn : taBd ≠ taBn := by decide
@[simp] theorem ta_taBd_ne_taE : taBd ≠ taE := by decide
@[simp] theorem ta_taBd_ne_taY : taBd ≠ taY := by decide
@[simp] theorem ta_taBd_ne_taA : taBd ≠ taA := by decide
@[simp] theorem ta_taBd_ne_taL : taBd ≠ taL := by decide
@[simp] theorem ta_taBd_ne_taR : taBd ≠ taR := by decide
@[simp] theorem ta_taBd_ne_lFl : taBd ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taBd : lFl ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDh : taBd ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taBd : lDh ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDt : taBd ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taBd : lDt ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDg : taBd ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taBd : lDg ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDi : taBd ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taBd : lDi ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lRp : taBd ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taBd : lRp ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lRn : taBd ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taBd : lRn ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDir : taBd ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taBd : lDir ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lFle : taBd ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taBd : lFle ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lKb : taBd ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taBd : lKb ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lCn : taBd ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taBd : lCn ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lSrc : taBd ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taBd : lSrc ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lDst : taBd ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taBd : lDst ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lCi : taBd ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taBd : lCi ≠ taBd := by decide
@[simp] theorem ta_taBd_ne_lCz : taBd ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taBd : lCz ≠ taBd := by decide
@[simp] theorem ta_taBn_ne_taT : taBn ≠ taT := by decide
@[simp] theorem ta_taBn_ne_taI : taBn ≠ taI := by decide
@[simp] theorem ta_taBn_ne_taUs : taBn ≠ taUs := by decide
@[simp] theorem ta_taBn_ne_taVa : taBn ≠ taVa := by decide
@[simp] theorem ta_taBn_ne_taPe : taBn ≠ taPe := by decide
@[simp] theorem ta_taBn_ne_taLp : taBn ≠ taLp := by decide
@[simp] theorem ta_taBn_ne_taLl : taBn ≠ taLl := by decide
@[simp] theorem ta_taBn_ne_taB : taBn ≠ taB := by decide
@[simp] theorem ta_taBn_ne_taBd : taBn ≠ taBd := by decide
@[simp] theorem ta_taBn_ne_taE : taBn ≠ taE := by decide
@[simp] theorem ta_taBn_ne_taY : taBn ≠ taY := by decide
@[simp] theorem ta_taBn_ne_taA : taBn ≠ taA := by decide
@[simp] theorem ta_taBn_ne_taL : taBn ≠ taL := by decide
@[simp] theorem ta_taBn_ne_taR : taBn ≠ taR := by decide
@[simp] theorem ta_taBn_ne_lFl : taBn ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taBn : lFl ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDh : taBn ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taBn : lDh ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDt : taBn ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taBn : lDt ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDg : taBn ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taBn : lDg ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDi : taBn ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taBn : lDi ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lRp : taBn ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taBn : lRp ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lRn : taBn ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taBn : lRn ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDir : taBn ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taBn : lDir ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lFle : taBn ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taBn : lFle ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lKb : taBn ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taBn : lKb ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lCn : taBn ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taBn : lCn ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lSrc : taBn ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taBn : lSrc ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lDst : taBn ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taBn : lDst ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lCi : taBn ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taBn : lCi ≠ taBn := by decide
@[simp] theorem ta_taBn_ne_lCz : taBn ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taBn : lCz ≠ taBn := by decide
@[simp] theorem ta_taE_ne_taT : taE ≠ taT := by decide
@[simp] theorem ta_taE_ne_taI : taE ≠ taI := by decide
@[simp] theorem ta_taE_ne_taUs : taE ≠ taUs := by decide
@[simp] theorem ta_taE_ne_taVa : taE ≠ taVa := by decide
@[simp] theorem ta_taE_ne_taPe : taE ≠ taPe := by decide
@[simp] theorem ta_taE_ne_taLp : taE ≠ taLp := by decide
@[simp] theorem ta_taE_ne_taLl : taE ≠ taLl := by decide
@[simp] theorem ta_taE_ne_taB : taE ≠ taB := by decide
@[simp] theorem ta_taE_ne_taBd : taE ≠ taBd := by decide
@[simp] theorem ta_taE_ne_taBn : taE ≠ taBn := by decide
@[simp] theorem ta_taE_ne_taY : taE ≠ taY := by decide
@[simp] theorem ta_taE_ne_taA : taE ≠ taA := by decide
@[simp] theorem ta_taE_ne_taL : taE ≠ taL := by decide
@[simp] theorem ta_taE_ne_taR : taE ≠ taR := by decide
@[simp] theorem ta_taE_ne_lFl : taE ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taE : lFl ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDh : taE ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taE : lDh ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDt : taE ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taE : lDt ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDg : taE ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taE : lDg ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDi : taE ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taE : lDi ≠ taE := by decide
@[simp] theorem ta_taE_ne_lRp : taE ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taE : lRp ≠ taE := by decide
@[simp] theorem ta_taE_ne_lRn : taE ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taE : lRn ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDir : taE ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taE : lDir ≠ taE := by decide
@[simp] theorem ta_taE_ne_lFle : taE ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taE : lFle ≠ taE := by decide
@[simp] theorem ta_taE_ne_lKb : taE ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taE : lKb ≠ taE := by decide
@[simp] theorem ta_taE_ne_lCn : taE ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taE : lCn ≠ taE := by decide
@[simp] theorem ta_taE_ne_lSrc : taE ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taE : lSrc ≠ taE := by decide
@[simp] theorem ta_taE_ne_lDst : taE ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taE : lDst ≠ taE := by decide
@[simp] theorem ta_taE_ne_lCi : taE ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taE : lCi ≠ taE := by decide
@[simp] theorem ta_taE_ne_lCz : taE ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taE : lCz ≠ taE := by decide
@[simp] theorem ta_taY_ne_taT : taY ≠ taT := by decide
@[simp] theorem ta_taY_ne_taI : taY ≠ taI := by decide
@[simp] theorem ta_taY_ne_taUs : taY ≠ taUs := by decide
@[simp] theorem ta_taY_ne_taVa : taY ≠ taVa := by decide
@[simp] theorem ta_taY_ne_taPe : taY ≠ taPe := by decide
@[simp] theorem ta_taY_ne_taLp : taY ≠ taLp := by decide
@[simp] theorem ta_taY_ne_taLl : taY ≠ taLl := by decide
@[simp] theorem ta_taY_ne_taB : taY ≠ taB := by decide
@[simp] theorem ta_taY_ne_taBd : taY ≠ taBd := by decide
@[simp] theorem ta_taY_ne_taBn : taY ≠ taBn := by decide
@[simp] theorem ta_taY_ne_taE : taY ≠ taE := by decide
@[simp] theorem ta_taY_ne_taA : taY ≠ taA := by decide
@[simp] theorem ta_taY_ne_taL : taY ≠ taL := by decide
@[simp] theorem ta_taY_ne_taR : taY ≠ taR := by decide
@[simp] theorem ta_taY_ne_lFl : taY ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taY : lFl ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDh : taY ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taY : lDh ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDt : taY ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taY : lDt ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDg : taY ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taY : lDg ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDi : taY ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taY : lDi ≠ taY := by decide
@[simp] theorem ta_taY_ne_lRp : taY ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taY : lRp ≠ taY := by decide
@[simp] theorem ta_taY_ne_lRn : taY ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taY : lRn ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDir : taY ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taY : lDir ≠ taY := by decide
@[simp] theorem ta_taY_ne_lFle : taY ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taY : lFle ≠ taY := by decide
@[simp] theorem ta_taY_ne_lKb : taY ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taY : lKb ≠ taY := by decide
@[simp] theorem ta_taY_ne_lCn : taY ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taY : lCn ≠ taY := by decide
@[simp] theorem ta_taY_ne_lSrc : taY ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taY : lSrc ≠ taY := by decide
@[simp] theorem ta_taY_ne_lDst : taY ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taY : lDst ≠ taY := by decide
@[simp] theorem ta_taY_ne_lCi : taY ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taY : lCi ≠ taY := by decide
@[simp] theorem ta_taY_ne_lCz : taY ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taY : lCz ≠ taY := by decide
@[simp] theorem ta_taA_ne_taT : taA ≠ taT := by decide
@[simp] theorem ta_taA_ne_taI : taA ≠ taI := by decide
@[simp] theorem ta_taA_ne_taUs : taA ≠ taUs := by decide
@[simp] theorem ta_taA_ne_taVa : taA ≠ taVa := by decide
@[simp] theorem ta_taA_ne_taPe : taA ≠ taPe := by decide
@[simp] theorem ta_taA_ne_taLp : taA ≠ taLp := by decide
@[simp] theorem ta_taA_ne_taLl : taA ≠ taLl := by decide
@[simp] theorem ta_taA_ne_taB : taA ≠ taB := by decide
@[simp] theorem ta_taA_ne_taBd : taA ≠ taBd := by decide
@[simp] theorem ta_taA_ne_taBn : taA ≠ taBn := by decide
@[simp] theorem ta_taA_ne_taE : taA ≠ taE := by decide
@[simp] theorem ta_taA_ne_taY : taA ≠ taY := by decide
@[simp] theorem ta_taA_ne_taL : taA ≠ taL := by decide
@[simp] theorem ta_taA_ne_taR : taA ≠ taR := by decide
@[simp] theorem ta_taA_ne_lFl : taA ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taA : lFl ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDh : taA ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taA : lDh ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDt : taA ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taA : lDt ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDg : taA ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taA : lDg ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDi : taA ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taA : lDi ≠ taA := by decide
@[simp] theorem ta_taA_ne_lRp : taA ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taA : lRp ≠ taA := by decide
@[simp] theorem ta_taA_ne_lRn : taA ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taA : lRn ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDir : taA ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taA : lDir ≠ taA := by decide
@[simp] theorem ta_taA_ne_lFle : taA ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taA : lFle ≠ taA := by decide
@[simp] theorem ta_taA_ne_lKb : taA ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taA : lKb ≠ taA := by decide
@[simp] theorem ta_taA_ne_lCn : taA ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taA : lCn ≠ taA := by decide
@[simp] theorem ta_taA_ne_lSrc : taA ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taA : lSrc ≠ taA := by decide
@[simp] theorem ta_taA_ne_lDst : taA ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taA : lDst ≠ taA := by decide
@[simp] theorem ta_taA_ne_lCi : taA ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taA : lCi ≠ taA := by decide
@[simp] theorem ta_taA_ne_lCz : taA ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taA : lCz ≠ taA := by decide
@[simp] theorem ta_taL_ne_taT : taL ≠ taT := by decide
@[simp] theorem ta_taL_ne_taI : taL ≠ taI := by decide
@[simp] theorem ta_taL_ne_taUs : taL ≠ taUs := by decide
@[simp] theorem ta_taL_ne_taVa : taL ≠ taVa := by decide
@[simp] theorem ta_taL_ne_taPe : taL ≠ taPe := by decide
@[simp] theorem ta_taL_ne_taLp : taL ≠ taLp := by decide
@[simp] theorem ta_taL_ne_taLl : taL ≠ taLl := by decide
@[simp] theorem ta_taL_ne_taB : taL ≠ taB := by decide
@[simp] theorem ta_taL_ne_taBd : taL ≠ taBd := by decide
@[simp] theorem ta_taL_ne_taBn : taL ≠ taBn := by decide
@[simp] theorem ta_taL_ne_taE : taL ≠ taE := by decide
@[simp] theorem ta_taL_ne_taY : taL ≠ taY := by decide
@[simp] theorem ta_taL_ne_taA : taL ≠ taA := by decide
@[simp] theorem ta_taL_ne_taR : taL ≠ taR := by decide
@[simp] theorem ta_taL_ne_lFl : taL ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taL : lFl ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDh : taL ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taL : lDh ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDt : taL ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taL : lDt ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDg : taL ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taL : lDg ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDi : taL ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taL : lDi ≠ taL := by decide
@[simp] theorem ta_taL_ne_lRp : taL ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taL : lRp ≠ taL := by decide
@[simp] theorem ta_taL_ne_lRn : taL ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taL : lRn ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDir : taL ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taL : lDir ≠ taL := by decide
@[simp] theorem ta_taL_ne_lFle : taL ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taL : lFle ≠ taL := by decide
@[simp] theorem ta_taL_ne_lKb : taL ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taL : lKb ≠ taL := by decide
@[simp] theorem ta_taL_ne_lCn : taL ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taL : lCn ≠ taL := by decide
@[simp] theorem ta_taL_ne_lSrc : taL ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taL : lSrc ≠ taL := by decide
@[simp] theorem ta_taL_ne_lDst : taL ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taL : lDst ≠ taL := by decide
@[simp] theorem ta_taL_ne_lCi : taL ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taL : lCi ≠ taL := by decide
@[simp] theorem ta_taL_ne_lCz : taL ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taL : lCz ≠ taL := by decide
@[simp] theorem ta_taR_ne_taT : taR ≠ taT := by decide
@[simp] theorem ta_taR_ne_taI : taR ≠ taI := by decide
@[simp] theorem ta_taR_ne_taUs : taR ≠ taUs := by decide
@[simp] theorem ta_taR_ne_taVa : taR ≠ taVa := by decide
@[simp] theorem ta_taR_ne_taPe : taR ≠ taPe := by decide
@[simp] theorem ta_taR_ne_taLp : taR ≠ taLp := by decide
@[simp] theorem ta_taR_ne_taLl : taR ≠ taLl := by decide
@[simp] theorem ta_taR_ne_taB : taR ≠ taB := by decide
@[simp] theorem ta_taR_ne_taBd : taR ≠ taBd := by decide
@[simp] theorem ta_taR_ne_taBn : taR ≠ taBn := by decide
@[simp] theorem ta_taR_ne_taE : taR ≠ taE := by decide
@[simp] theorem ta_taR_ne_taY : taR ≠ taY := by decide
@[simp] theorem ta_taR_ne_taA : taR ≠ taA := by decide
@[simp] theorem ta_taR_ne_taL : taR ≠ taL := by decide
@[simp] theorem ta_taR_ne_lFl : taR ≠ lFl := by decide
@[simp] theorem ta_lFl_ne_taR : lFl ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDh : taR ≠ lDh := by decide
@[simp] theorem ta_lDh_ne_taR : lDh ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDt : taR ≠ lDt := by decide
@[simp] theorem ta_lDt_ne_taR : lDt ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDg : taR ≠ lDg := by decide
@[simp] theorem ta_lDg_ne_taR : lDg ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDi : taR ≠ lDi := by decide
@[simp] theorem ta_lDi_ne_taR : lDi ≠ taR := by decide
@[simp] theorem ta_taR_ne_lRp : taR ≠ lRp := by decide
@[simp] theorem ta_lRp_ne_taR : lRp ≠ taR := by decide
@[simp] theorem ta_taR_ne_lRn : taR ≠ lRn := by decide
@[simp] theorem ta_lRn_ne_taR : lRn ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDir : taR ≠ lDir := by decide
@[simp] theorem ta_lDir_ne_taR : lDir ≠ taR := by decide
@[simp] theorem ta_taR_ne_lFle : taR ≠ lFle := by decide
@[simp] theorem ta_lFle_ne_taR : lFle ≠ taR := by decide
@[simp] theorem ta_taR_ne_lKb : taR ≠ lKb := by decide
@[simp] theorem ta_lKb_ne_taR : lKb ≠ taR := by decide
@[simp] theorem ta_taR_ne_lCn : taR ≠ lCn := by decide
@[simp] theorem ta_lCn_ne_taR : lCn ≠ taR := by decide
@[simp] theorem ta_taR_ne_lSrc : taR ≠ lSrc := by decide
@[simp] theorem ta_lSrc_ne_taR : lSrc ≠ taR := by decide
@[simp] theorem ta_taR_ne_lDst : taR ≠ lDst := by decide
@[simp] theorem ta_lDst_ne_taR : lDst ≠ taR := by decide
@[simp] theorem ta_taR_ne_lCi : taR ≠ lCi := by decide
@[simp] theorem ta_lCi_ne_taR : lCi ≠ taR := by decide
@[simp] theorem ta_taR_ne_lCz : taR ≠ lCz := by decide
@[simp] theorem ta_lCz_ne_taR : lCz ≠ taR := by decide

theorem ecell_idx (C : Ctx) (o i : Nat) : ecell C o + (BitVec.ofNat 64 i * 8#64 + 8#64) = ecell C (o + 1 + i) := by
  rw [show BitVec.ofNat 64 i * 8#64 + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) from Big.add8_eq i]
  unfold ecell; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

def taParams : List MlS := [taT, taI, taUs, taVa, taPe]
def taLocals : List MlS := [taLp, taLl, taB, taBd, taBn, taE, taY, taA, taL, taR, lCn, lSrc, lDst, lCi, lCz]

def taBody (C : Ctx) : ProgHOL 64 := prologue taLocals
  (.seq (.assign .local taLp (.load .one (.op .add [(vv taT), (.const 8)]))) (.seq (.assign .local taLl (.load .one (vv taLp))) (.seq (.assign .local lCn (.op .add [(vv taLl), (.const 1)])) (allocP C taB (.panop .mul [vv lCn, .const 8]) (.seq (.assign .local lSrc (vv taLp)) (.seq (.assign .local lDst (vv taB)) (.seq (.assign .local lCi (.const 0)) (.seq copyLoop (.seq (.assign .local taBd (.load .one (.op .add [(vv taT), (.const 40)]))) (.seq (.assign .local taBn (.load .one (vv taBd))) (.ite (.cmp .lower (vv taI) (vv taBn)) (.seq (.assign .local taE (.load .one (.op .add [(vv taBd), (.op .add [.panop .mul [vv taI, .const 8], .const 8])]))) (.seq (.call (some (some (.local, taY), none)) fInstLPF [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv taE), (vv taB), (vv taUs)]) (.seq (.call (some (some (.local, taA), none)) ExPre.fAppend [(vv taVa), (vv taPe)]) (.seq (.assign .local taL (.load .one (vv taA))) (.seq (.call (some (some (.local, taR), none)) ExQ.fIrr [(vv taA), (.const 0), (vv taL), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv taY), (.const 0)]) (.return (vv taR))))))) hang)))))))))))

section
variable {σ : Type}

theorem ta_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ taLocals → (ctxEnv C ++ taParams.zip vals).get x = none :=
  Knot.params_none C taLocals taParams vals (by decide) (by decide)

structure TaCodes (C : Ctx) : Prop where
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  self : C.code.lookup fTa = some (taParams.map (fun p => (p, ShapeHOL.one)), taBody C, .one)

theorem ta_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TaCodes C)
    (tbl : IProjTable) (ot : Nat) (htb : TblE C.EB C.EH ot tbl) (i : Nat) (hi : i < 2 ^ 63) (us : LsIdx)
    (targs : List EIdx) (pe : EIdx) (H : List (BitVec 64)) (oa : Nat) (hp : C.H <+: H)
    (hba : BlkAt H oa (targs.map Enc.idxW)) (s : AState)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns tbl.levelParams = some ks)
    (vs : List ConLeche.Level) (hus : denoteLs s.store.lss us = some vs)
    (hst : StateOK s) (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store) (hden : ∀ b ∈ tbl.bodies.toList, (denoteE s.store b).isSome = true)
    (hlen : tbl.levelParams.length + 1 < 2 ^ 60) :
    SpecR (σ := σ) (Pre (ctxH C H) s (taParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C oa,
      Enc.idxW pe])) (taBody C) s ((tbl.entry i).typeAt us targs pe) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (ta_none _ _) ?_
  obtain ⟨-, ⟨wl, hwl, oL, hwL, hblk⟩, -, -, -, ⟨wb, hwb, oB, hwB, hbb⟩⟩ := htb
  subst hwL hwB
  refine specR_envLoadI (C := ctxH C H) taLp (.op .add [vv taT, .const 8]) (ot + 1) _ (by decide)
    (by simp +decide [sev, Env.get, taParams, ctxEnv]; exact (by simpa using ecell_add C ot 1 : ecell C ot + 8#64 = ecell C (ot + 1))) hwl ?_
  have hl0 : C.EH[oL]? = some (BitVec.ofNat 64 tbl.levelParams.length) := by simpa using hblk.1
  refine specR_envLoadI (C := ctxH C H) taLl (vv taLp) oL _ (by decide) (by simp +decide [Env.get]; rfl) hl0 ?_
  refine specR_assignI lCn _ (BitVec.ofNat 64 (tbl.levelParams.length + 1)) (by decide)
    (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
  refine specR_allocI (C := ctxH C H) taB (.panop .mul [vv lCn, .const 8]) (tbl.levelParams.length + 1)
    (by omega) (by decide) (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _)
    (fun H' wsN hpre hwl2 hcap => ?_)
  refine specR_assignI lSrc (vv taLp) (ecell C oL) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
  refine specR_assignI lDst (vv taB) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
  refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
  have hws : (BitVec.ofNat 64 tbl.levelParams.length :: tbl.levelParams.map Enc.idxW).length =
      tbl.levelParams.length + 1 := by simp
  refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 tbl.levelParams.length :: tbl.levelParams.map Enc.idxW)
    oL H'.length (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
    (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, taParams, ctxEnv]) ?_
  · rcases j with _ | j
    · simpa using hl0
    · have := hblk.2 j (by simp at hj ⊢; omega)
      simp only [List.getElem_cons_succ]
      rw [show oL + (j + 1) = oL + 1 + j by omega]; simpa using this
  have hblk2 := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 tbl.levelParams.length :: tbl.levelParams.map Enc.idxW)
    H'.length (tbl.levelParams.map Enc.idxW) (by simp) (by simp [hwl2])
  have hPF0 : H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 tbl.levelParams.length :: tbl.levelParams.map Enc.idxW)
      H'.length (BitVec.ofNat 64 tbl.levelParams.length :: tbl.levelParams.map Enc.idxW).length :=
    prefix_fillI _ _ _ H (hpre.length_le) (hpre.trans (List.prefix_append _ _)) _
  refine specR_envLoadI (C := ctxH C _) taBd (.op .add [vv taT, .const 40]) (ot + 5) _ (by decide)
    (by simp +decide [sev, Env.get, taParams, ctxEnv]; exact (by simpa using ecell_add C ot 5 : ecell C ot + 40#64 = ecell C (ot + 5))) hwb ?_
  have hb0 : C.EH[oB]? = some (BitVec.ofNat 64 tbl.bodies.size) := by simpa using hbb.1
  refine specR_envLoadI (C := ctxH C _) taBn (vv taBd) oB _ (by decide) (by simp +decide [Env.get]; rfl) hb0 ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hbsz : tbl.bodies.size < 2 ^ 63 := by
    have h1 := blkAt_len (show BlkAt C.EH oB (tbl.bodies.toList.map Enc.idxW) from hbb)
    have h2 : C.EH.length ≤ C.EN := ht0.sr.env.1.len
    have h3 := hok.envLay
    simp only [List.length_map, Array.length_toList] at h1; omega
  have hlw := word_lt_iff i tbl.bodies.size (by unfold B; omega) (by unfold B; omega)
  by_cases hib : i < tbl.bodies.size
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get, taParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr hib]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, taParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    hlw.mpr hib]) (fun _ => ?_) (fun h => absurd h (by decide))
  have hbi : C.EH[oB + 1 + i]? = some (Enc.idxW tbl.bodies[i]) := by
    have := hbb.2 i (by simpa using hib); simpa using this
  refine specR_envLoadI (C := ctxH C _) taE (.op .add [vv taBd, .op .add [.panop .mul [vv taI, .const 8], .const 8]])
    (oB + 1 + i) _ (by decide) (by simp +decide [sev, Env.get, taParams, ctxEnv]; exact ecell_idx C oB i) hbi ?_
  unfold IProjEntry.typeAt
  simp only [IProjTable.entry, Array.getD, hib, dite_true]
  refine specR_callNIH taY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv taE, vv taB, vv taUs]
    (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW tbl.bodies[i], cellA C H'.length, Enc.idxW us] (by decide) rfl
    (by decide) hc.ilpf
    ⟨rfl, by simp, by simp +decide [sev, Env.get]; rfl, by simp +decide [Env.get, taParams, ctxEnv], trivial⟩
    (PostILP (ctxH C _)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp', hw, hsr⟩ => ⟨H'', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt H'.length tbl.levelParams ks us vs _ s tbl.bodies[i]
        hks hus hst hrn hrl hrls (hden _ (by simp)) hblk2))
    (fun b w s2 H2 hp2 hw => ?_)
  subst hw
  refine ExPre.specR_callApp (C := ctxH C H2) (ctxOK_H hok H2) hc.app taA (vv taVa) (vv taPe) oa (targs.map Enc.idxW)
    (Enc.idxW pe) (by decide) (blkAt_mono hba (hPF0.trans hp2)) (by simp +decide [Env.get, taParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, taParams, ctxEnv]) (fun H3 o3 hp3 hb3 => ?_)
  have hb3' : BlkAt H3 o3 ((targs ++ [pe]).toArray.toList.map Enc.idxW) := by simpa using hb3
  refine specR_atEntry fun t1 ht1 => ?_
  have hsm := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht1.sr hb3'
  simp only [List.length_map, Array.length_toList, List.length_append, List.length_singleton] at hsm
  obtain ⟨hlo3, hlv3⟩ := blkAt_get0 hb3'
  refine UD.specR_heapLoadI' (C := ctxH C H3) taL (vv taA) o3 (BitVec.ofNat 64 (targs.length + 1))
    (by show H3[o3]? = _; rw [List.getElem?_eq_getElem hlo3, hlv3]; simp) (by decide) (by simp; rfl) ?_
  rw [show targs.toArray.push pe = (targs ++ [pe]).toArray by simp]
  simp only [instantiateListFast]
  refine specR_congr (m' := instantiateRevRange coreWalkFuel b (targs ++ [pe]).toArray 0 (targs ++ [pe]).toArray.size 0
    >>= fun r => pure r) (by simp) ?_
  refine ILP.callE_spec (C := ctxH C H3) taR ExQ.fIrr ExQ.irrParams
    [vv taA, .const 0, vv taL, .const (BitVec.ofNat 64 coreWalkFuel), vv taY, .const 0] (ExQ.irrBody C)
    [cellA C o3, BitVec.ofNat 64 0, BitVec.ofNat 64 (targs ++ [pe]).toArray.size, BitVec.ofNat 64 coreWalkFuel,
      Enc.idxW b, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
    ⟨by simp <;> rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
    (ExQ.irr_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesQ_H hc.q H3) (targs ++ [pe]).toArray o3 hb3' (by simp; omega)
      s2 coreWalkFuel 0 (targs ++ [pe]).toArray.size 0 b CV.coreWalkFuel_lt (by decide) (by simp; omega) (by decide))
    (fun r s3 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨H3, hPF0.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
