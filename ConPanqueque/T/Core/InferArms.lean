import ConPanqueque.T.Core.InferBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `inferBody`'s small arms: sort, constant, `let`
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def isS := ofString "is_s"
def isR := ofString "is_r"

@[simp] theorem ia_isS_ne_isR : isS ≠ isR := by decide
@[simp] theorem ia_isS_ne_lKb : isS ≠ lKb := by decide
@[simp] theorem ia_isS_ne_ibU : isS ≠ ibU := by decide
@[simp] theorem ia_isR_ne_isS : isR ≠ isS := by decide
@[simp] theorem ia_isR_ne_lKb : isR ≠ lKb := by decide
@[simp] theorem ia_isR_ne_ibU : isR ≠ ibU := by decide
@[simp] theorem ia_lKb_ne_isS : lKb ≠ isS := by decide
@[simp] theorem ia_lKb_ne_isR : lKb ≠ isR := by decide
@[simp] theorem ia_ibU_ne_isS : ibU ≠ isS := by decide
@[simp] theorem ia_ibU_ne_isR : ibU ≠ isR := by decide

def isLocals : List MlS := [isS, isR]

def isBody : ProgHOL 64 := prologue isLocals
  (.seq (.call (some (some (.local, isS), none)) fInternLSucc [vv ibU])
  (.seq (.call (some (some (.local, isR), none)) fInternSort [vv isS]) (.return (vv isR))))

def ikW := ofString "icn_w"
def ikQ := ofString "icn_q"
def ikLp := ofString "icn_lp"
def ikLl := ofString "icn_ll"
def ikNm := ofString "icn_nm"
def ikTy := ofString "icn_ty"
def ikX := ofString "icn_x"

@[simp] theorem ik_icW_ne_icQ : ikW ≠ ikQ := by decide
@[simp] theorem ik_icW_ne_icLp : ikW ≠ ikLp := by decide
@[simp] theorem ik_icW_ne_icLl : ikW ≠ ikLl := by decide
@[simp] theorem ik_icW_ne_icNm : ikW ≠ ikNm := by decide
@[simp] theorem ik_icW_ne_icTy : ikW ≠ ikTy := by decide
@[simp] theorem ik_icW_ne_icX : ikW ≠ ikX := by decide
@[simp] theorem ik_icW_ne_lKb : ikW ≠ lKb := by decide
@[simp] theorem ik_icW_ne_ibN : ikW ≠ ibN := by decide
@[simp] theorem ik_icW_ne_ibUs : ikW ≠ ibUs := by decide
@[simp] theorem ik_icW_ne_lFl : ikW ≠ lFl := by decide
@[simp] theorem ik_icW_ne_lDh : ikW ≠ lDh := by decide
@[simp] theorem ik_icW_ne_lDt : ikW ≠ lDt := by decide
@[simp] theorem ik_icW_ne_lDg : ikW ≠ lDg := by decide
@[simp] theorem ik_icW_ne_lDi : ikW ≠ lDi := by decide
@[simp] theorem ik_icW_ne_lRp : ikW ≠ lRp := by decide
@[simp] theorem ik_icW_ne_lRn : ikW ≠ lRn := by decide
@[simp] theorem ik_icW_ne_lFls : ikW ≠ lFls := by decide
@[simp] theorem ik_icW_ne_lDir : ikW ≠ lDir := by decide
@[simp] theorem ik_icQ_ne_icW : ikQ ≠ ikW := by decide
@[simp] theorem ik_icQ_ne_icLp : ikQ ≠ ikLp := by decide
@[simp] theorem ik_icQ_ne_icLl : ikQ ≠ ikLl := by decide
@[simp] theorem ik_icQ_ne_icNm : ikQ ≠ ikNm := by decide
@[simp] theorem ik_icQ_ne_icTy : ikQ ≠ ikTy := by decide
@[simp] theorem ik_icQ_ne_icX : ikQ ≠ ikX := by decide
@[simp] theorem ik_icQ_ne_lKb : ikQ ≠ lKb := by decide
@[simp] theorem ik_icQ_ne_ibN : ikQ ≠ ibN := by decide
@[simp] theorem ik_icQ_ne_ibUs : ikQ ≠ ibUs := by decide
@[simp] theorem ik_icQ_ne_lFl : ikQ ≠ lFl := by decide
@[simp] theorem ik_icQ_ne_lDh : ikQ ≠ lDh := by decide
@[simp] theorem ik_icQ_ne_lDt : ikQ ≠ lDt := by decide
@[simp] theorem ik_icQ_ne_lDg : ikQ ≠ lDg := by decide
@[simp] theorem ik_icQ_ne_lDi : ikQ ≠ lDi := by decide
@[simp] theorem ik_icQ_ne_lRp : ikQ ≠ lRp := by decide
@[simp] theorem ik_icQ_ne_lRn : ikQ ≠ lRn := by decide
@[simp] theorem ik_icQ_ne_lFls : ikQ ≠ lFls := by decide
@[simp] theorem ik_icQ_ne_lDir : ikQ ≠ lDir := by decide
@[simp] theorem ik_icLp_ne_icW : ikLp ≠ ikW := by decide
@[simp] theorem ik_icLp_ne_icQ : ikLp ≠ ikQ := by decide
@[simp] theorem ik_icLp_ne_icLl : ikLp ≠ ikLl := by decide
@[simp] theorem ik_icLp_ne_icNm : ikLp ≠ ikNm := by decide
@[simp] theorem ik_icLp_ne_icTy : ikLp ≠ ikTy := by decide
@[simp] theorem ik_icLp_ne_icX : ikLp ≠ ikX := by decide
@[simp] theorem ik_icLp_ne_lKb : ikLp ≠ lKb := by decide
@[simp] theorem ik_icLp_ne_ibN : ikLp ≠ ibN := by decide
@[simp] theorem ik_icLp_ne_ibUs : ikLp ≠ ibUs := by decide
@[simp] theorem ik_icLp_ne_lFl : ikLp ≠ lFl := by decide
@[simp] theorem ik_icLp_ne_lDh : ikLp ≠ lDh := by decide
@[simp] theorem ik_icLp_ne_lDt : ikLp ≠ lDt := by decide
@[simp] theorem ik_icLp_ne_lDg : ikLp ≠ lDg := by decide
@[simp] theorem ik_icLp_ne_lDi : ikLp ≠ lDi := by decide
@[simp] theorem ik_icLp_ne_lRp : ikLp ≠ lRp := by decide
@[simp] theorem ik_icLp_ne_lRn : ikLp ≠ lRn := by decide
@[simp] theorem ik_icLp_ne_lFls : ikLp ≠ lFls := by decide
@[simp] theorem ik_icLp_ne_lDir : ikLp ≠ lDir := by decide
@[simp] theorem ik_icLl_ne_icW : ikLl ≠ ikW := by decide
@[simp] theorem ik_icLl_ne_icQ : ikLl ≠ ikQ := by decide
@[simp] theorem ik_icLl_ne_icLp : ikLl ≠ ikLp := by decide
@[simp] theorem ik_icLl_ne_icNm : ikLl ≠ ikNm := by decide
@[simp] theorem ik_icLl_ne_icTy : ikLl ≠ ikTy := by decide
@[simp] theorem ik_icLl_ne_icX : ikLl ≠ ikX := by decide
@[simp] theorem ik_icLl_ne_lKb : ikLl ≠ lKb := by decide
@[simp] theorem ik_icLl_ne_ibN : ikLl ≠ ibN := by decide
@[simp] theorem ik_icLl_ne_ibUs : ikLl ≠ ibUs := by decide
@[simp] theorem ik_icLl_ne_lFl : ikLl ≠ lFl := by decide
@[simp] theorem ik_icLl_ne_lDh : ikLl ≠ lDh := by decide
@[simp] theorem ik_icLl_ne_lDt : ikLl ≠ lDt := by decide
@[simp] theorem ik_icLl_ne_lDg : ikLl ≠ lDg := by decide
@[simp] theorem ik_icLl_ne_lDi : ikLl ≠ lDi := by decide
@[simp] theorem ik_icLl_ne_lRp : ikLl ≠ lRp := by decide
@[simp] theorem ik_icLl_ne_lRn : ikLl ≠ lRn := by decide
@[simp] theorem ik_icLl_ne_lFls : ikLl ≠ lFls := by decide
@[simp] theorem ik_icLl_ne_lDir : ikLl ≠ lDir := by decide
@[simp] theorem ik_icNm_ne_icW : ikNm ≠ ikW := by decide
@[simp] theorem ik_icNm_ne_icQ : ikNm ≠ ikQ := by decide
@[simp] theorem ik_icNm_ne_icLp : ikNm ≠ ikLp := by decide
@[simp] theorem ik_icNm_ne_icLl : ikNm ≠ ikLl := by decide
@[simp] theorem ik_icNm_ne_icTy : ikNm ≠ ikTy := by decide
@[simp] theorem ik_icNm_ne_icX : ikNm ≠ ikX := by decide
@[simp] theorem ik_icNm_ne_lKb : ikNm ≠ lKb := by decide
@[simp] theorem ik_icNm_ne_ibN : ikNm ≠ ibN := by decide
@[simp] theorem ik_icNm_ne_ibUs : ikNm ≠ ibUs := by decide
@[simp] theorem ik_icNm_ne_lFl : ikNm ≠ lFl := by decide
@[simp] theorem ik_icNm_ne_lDh : ikNm ≠ lDh := by decide
@[simp] theorem ik_icNm_ne_lDt : ikNm ≠ lDt := by decide
@[simp] theorem ik_icNm_ne_lDg : ikNm ≠ lDg := by decide
@[simp] theorem ik_icNm_ne_lDi : ikNm ≠ lDi := by decide
@[simp] theorem ik_icNm_ne_lRp : ikNm ≠ lRp := by decide
@[simp] theorem ik_icNm_ne_lRn : ikNm ≠ lRn := by decide
@[simp] theorem ik_icNm_ne_lFls : ikNm ≠ lFls := by decide
@[simp] theorem ik_icNm_ne_lDir : ikNm ≠ lDir := by decide
@[simp] theorem ik_icTy_ne_icW : ikTy ≠ ikW := by decide
@[simp] theorem ik_icTy_ne_icQ : ikTy ≠ ikQ := by decide
@[simp] theorem ik_icTy_ne_icLp : ikTy ≠ ikLp := by decide
@[simp] theorem ik_icTy_ne_icLl : ikTy ≠ ikLl := by decide
@[simp] theorem ik_icTy_ne_icNm : ikTy ≠ ikNm := by decide
@[simp] theorem ik_icTy_ne_icX : ikTy ≠ ikX := by decide
@[simp] theorem ik_icTy_ne_lKb : ikTy ≠ lKb := by decide
@[simp] theorem ik_icTy_ne_ibN : ikTy ≠ ibN := by decide
@[simp] theorem ik_icTy_ne_ibUs : ikTy ≠ ibUs := by decide
@[simp] theorem ik_icTy_ne_lFl : ikTy ≠ lFl := by decide
@[simp] theorem ik_icTy_ne_lDh : ikTy ≠ lDh := by decide
@[simp] theorem ik_icTy_ne_lDt : ikTy ≠ lDt := by decide
@[simp] theorem ik_icTy_ne_lDg : ikTy ≠ lDg := by decide
@[simp] theorem ik_icTy_ne_lDi : ikTy ≠ lDi := by decide
@[simp] theorem ik_icTy_ne_lRp : ikTy ≠ lRp := by decide
@[simp] theorem ik_icTy_ne_lRn : ikTy ≠ lRn := by decide
@[simp] theorem ik_icTy_ne_lFls : ikTy ≠ lFls := by decide
@[simp] theorem ik_icTy_ne_lDir : ikTy ≠ lDir := by decide
@[simp] theorem ik_icX_ne_icW : ikX ≠ ikW := by decide
@[simp] theorem ik_icX_ne_icQ : ikX ≠ ikQ := by decide
@[simp] theorem ik_icX_ne_icLp : ikX ≠ ikLp := by decide
@[simp] theorem ik_icX_ne_icLl : ikX ≠ ikLl := by decide
@[simp] theorem ik_icX_ne_icNm : ikX ≠ ikNm := by decide
@[simp] theorem ik_icX_ne_icTy : ikX ≠ ikTy := by decide
@[simp] theorem ik_icX_ne_lKb : ikX ≠ lKb := by decide
@[simp] theorem ik_icX_ne_ibN : ikX ≠ ibN := by decide
@[simp] theorem ik_icX_ne_ibUs : ikX ≠ ibUs := by decide
@[simp] theorem ik_icX_ne_lFl : ikX ≠ lFl := by decide
@[simp] theorem ik_icX_ne_lDh : ikX ≠ lDh := by decide
@[simp] theorem ik_icX_ne_lDt : ikX ≠ lDt := by decide
@[simp] theorem ik_icX_ne_lDg : ikX ≠ lDg := by decide
@[simp] theorem ik_icX_ne_lDi : ikX ≠ lDi := by decide
@[simp] theorem ik_icX_ne_lRp : ikX ≠ lRp := by decide
@[simp] theorem ik_icX_ne_lRn : ikX ≠ lRn := by decide
@[simp] theorem ik_icX_ne_lFls : ikX ≠ lFls := by decide
@[simp] theorem ik_icX_ne_lDir : ikX ≠ lDir := by decide
@[simp] theorem ik_lKb_ne_icW : lKb ≠ ikW := by decide
@[simp] theorem ik_lKb_ne_icQ : lKb ≠ ikQ := by decide
@[simp] theorem ik_lKb_ne_icLp : lKb ≠ ikLp := by decide
@[simp] theorem ik_lKb_ne_icLl : lKb ≠ ikLl := by decide
@[simp] theorem ik_lKb_ne_icNm : lKb ≠ ikNm := by decide
@[simp] theorem ik_lKb_ne_icTy : lKb ≠ ikTy := by decide
@[simp] theorem ik_lKb_ne_icX : lKb ≠ ikX := by decide
@[simp] theorem ik_ibN_ne_icW : ibN ≠ ikW := by decide
@[simp] theorem ik_ibN_ne_icQ : ibN ≠ ikQ := by decide
@[simp] theorem ik_ibN_ne_icLp : ibN ≠ ikLp := by decide
@[simp] theorem ik_ibN_ne_icLl : ibN ≠ ikLl := by decide
@[simp] theorem ik_ibN_ne_icNm : ibN ≠ ikNm := by decide
@[simp] theorem ik_ibN_ne_icTy : ibN ≠ ikTy := by decide
@[simp] theorem ik_ibN_ne_icX : ibN ≠ ikX := by decide
@[simp] theorem ik_ibUs_ne_icW : ibUs ≠ ikW := by decide
@[simp] theorem ik_ibUs_ne_icQ : ibUs ≠ ikQ := by decide
@[simp] theorem ik_ibUs_ne_icLp : ibUs ≠ ikLp := by decide
@[simp] theorem ik_ibUs_ne_icLl : ibUs ≠ ikLl := by decide
@[simp] theorem ik_ibUs_ne_icNm : ibUs ≠ ikNm := by decide
@[simp] theorem ik_ibUs_ne_icTy : ibUs ≠ ikTy := by decide
@[simp] theorem ik_ibUs_ne_icX : ibUs ≠ ikX := by decide
@[simp] theorem ik_lFl_ne_icW : lFl ≠ ikW := by decide
@[simp] theorem ik_lFl_ne_icQ : lFl ≠ ikQ := by decide
@[simp] theorem ik_lFl_ne_icLp : lFl ≠ ikLp := by decide
@[simp] theorem ik_lFl_ne_icLl : lFl ≠ ikLl := by decide
@[simp] theorem ik_lFl_ne_icNm : lFl ≠ ikNm := by decide
@[simp] theorem ik_lFl_ne_icTy : lFl ≠ ikTy := by decide
@[simp] theorem ik_lFl_ne_icX : lFl ≠ ikX := by decide
@[simp] theorem ik_lDh_ne_icW : lDh ≠ ikW := by decide
@[simp] theorem ik_lDh_ne_icQ : lDh ≠ ikQ := by decide
@[simp] theorem ik_lDh_ne_icLp : lDh ≠ ikLp := by decide
@[simp] theorem ik_lDh_ne_icLl : lDh ≠ ikLl := by decide
@[simp] theorem ik_lDh_ne_icNm : lDh ≠ ikNm := by decide
@[simp] theorem ik_lDh_ne_icTy : lDh ≠ ikTy := by decide
@[simp] theorem ik_lDh_ne_icX : lDh ≠ ikX := by decide
@[simp] theorem ik_lDt_ne_icW : lDt ≠ ikW := by decide
@[simp] theorem ik_lDt_ne_icQ : lDt ≠ ikQ := by decide
@[simp] theorem ik_lDt_ne_icLp : lDt ≠ ikLp := by decide
@[simp] theorem ik_lDt_ne_icLl : lDt ≠ ikLl := by decide
@[simp] theorem ik_lDt_ne_icNm : lDt ≠ ikNm := by decide
@[simp] theorem ik_lDt_ne_icTy : lDt ≠ ikTy := by decide
@[simp] theorem ik_lDt_ne_icX : lDt ≠ ikX := by decide
@[simp] theorem ik_lDg_ne_icW : lDg ≠ ikW := by decide
@[simp] theorem ik_lDg_ne_icQ : lDg ≠ ikQ := by decide
@[simp] theorem ik_lDg_ne_icLp : lDg ≠ ikLp := by decide
@[simp] theorem ik_lDg_ne_icLl : lDg ≠ ikLl := by decide
@[simp] theorem ik_lDg_ne_icNm : lDg ≠ ikNm := by decide
@[simp] theorem ik_lDg_ne_icTy : lDg ≠ ikTy := by decide
@[simp] theorem ik_lDg_ne_icX : lDg ≠ ikX := by decide
@[simp] theorem ik_lDi_ne_icW : lDi ≠ ikW := by decide
@[simp] theorem ik_lDi_ne_icQ : lDi ≠ ikQ := by decide
@[simp] theorem ik_lDi_ne_icLp : lDi ≠ ikLp := by decide
@[simp] theorem ik_lDi_ne_icLl : lDi ≠ ikLl := by decide
@[simp] theorem ik_lDi_ne_icNm : lDi ≠ ikNm := by decide
@[simp] theorem ik_lDi_ne_icTy : lDi ≠ ikTy := by decide
@[simp] theorem ik_lDi_ne_icX : lDi ≠ ikX := by decide
@[simp] theorem ik_lRp_ne_icW : lRp ≠ ikW := by decide
@[simp] theorem ik_lRp_ne_icQ : lRp ≠ ikQ := by decide
@[simp] theorem ik_lRp_ne_icLp : lRp ≠ ikLp := by decide
@[simp] theorem ik_lRp_ne_icLl : lRp ≠ ikLl := by decide
@[simp] theorem ik_lRp_ne_icNm : lRp ≠ ikNm := by decide
@[simp] theorem ik_lRp_ne_icTy : lRp ≠ ikTy := by decide
@[simp] theorem ik_lRp_ne_icX : lRp ≠ ikX := by decide
@[simp] theorem ik_lRn_ne_icW : lRn ≠ ikW := by decide
@[simp] theorem ik_lRn_ne_icQ : lRn ≠ ikQ := by decide
@[simp] theorem ik_lRn_ne_icLp : lRn ≠ ikLp := by decide
@[simp] theorem ik_lRn_ne_icLl : lRn ≠ ikLl := by decide
@[simp] theorem ik_lRn_ne_icNm : lRn ≠ ikNm := by decide
@[simp] theorem ik_lRn_ne_icTy : lRn ≠ ikTy := by decide
@[simp] theorem ik_lRn_ne_icX : lRn ≠ ikX := by decide
@[simp] theorem ik_lFls_ne_icW : lFls ≠ ikW := by decide
@[simp] theorem ik_lFls_ne_icQ : lFls ≠ ikQ := by decide
@[simp] theorem ik_lFls_ne_icLp : lFls ≠ ikLp := by decide
@[simp] theorem ik_lFls_ne_icLl : lFls ≠ ikLl := by decide
@[simp] theorem ik_lFls_ne_icNm : lFls ≠ ikNm := by decide
@[simp] theorem ik_lFls_ne_icTy : lFls ≠ ikTy := by decide
@[simp] theorem ik_lFls_ne_icX : lFls ≠ ikX := by decide
@[simp] theorem ik_lDir_ne_icW : lDir ≠ ikW := by decide
@[simp] theorem ik_lDir_ne_icQ : lDir ≠ ikQ := by decide
@[simp] theorem ik_lDir_ne_icLp : lDir ≠ ikLp := by decide
@[simp] theorem ik_lDir_ne_icLl : lDir ≠ ikLl := by decide
@[simp] theorem ik_lDir_ne_icNm : lDir ≠ ikNm := by decide
@[simp] theorem ik_lDir_ne_icTy : lDir ≠ ikTy := by decide
@[simp] theorem ik_lDir_ne_icX : lDir ≠ ikX := by decide

def ikLocals : List MlS := [ikW, ikQ, ikLp, ikLl, lFl, lDh, lDt, lDg, lDi, lRp, lRn, ikNm, ikTy, ikX]

def ikCore (C : Ctx) : ProgHOL 64 :=
  envFindP C ikW (vv ibN)
  (.ite (.cmp .equal (vv ikW) (.const 0)) hang
  (.seq (.assign .local ikQ (.op .sub [vv ikW, .const 1]))
  (.seq (.assign .local ikLp (.load .one (.op .add [vv ikQ, .const 16])))
  (.seq (.assign .local ikLl (.load .one (vv ikLp)))
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv ibUs)) (.seq lsViewP
  (.ite (.cmp .notEqual (vv lRn) (vv ikLl)) hang
  (.seq (.assign .local ikNm (.load .one (.op .add [vv ikQ, .const 8])))
  (.seq (.assign .local ikTy (.load .one (.op .add [vv ikQ, .const 24])))
  (.seq (.call (some (some (.local, ikX), none)) CT.fCT [vv ikNm, vv ikLp, vv ikTy, vv ibUs]) (.return (vv ikX)))))))))))))

def ikBody (C : Ctx) : ProgHOL 64 := prologue ikLocals (ikCore C)

def ltA := ofString "ltn_a"
def ltH := ofString "ltn_h"
def ltB := ofString "ltn_b"
def ltD := ofString "ltn_d"
def ltO := ofString "ltn_o"
def ltR := ofString "ltn_r"

@[simp] theorem lt_ltA_ne_ltH : ltA ≠ ltH := by decide
@[simp] theorem lt_ltA_ne_ltB : ltA ≠ ltB := by decide
@[simp] theorem lt_ltA_ne_ltD : ltA ≠ ltD := by decide
@[simp] theorem lt_ltA_ne_ltO : ltA ≠ ltO := by decide
@[simp] theorem lt_ltA_ne_ltR : ltA ≠ ltR := by decide
@[simp] theorem lt_ltA_ne_lKb : ltA ≠ lKb := by decide
@[simp] theorem lt_ltA_ne_kFu : ltA ≠ kFu := by decide
@[simp] theorem lt_ltA_ne_kD : ltA ≠ kD := by decide
@[simp] theorem lt_ltA_ne_ibT1 : ltA ≠ ibT1 := by decide
@[simp] theorem lt_ltA_ne_ibV1 : ltA ≠ ibV1 := by decide
@[simp] theorem lt_ltA_ne_ibB1 : ltA ≠ ibB1 := by decide
@[simp] theorem lt_ltA_ne_lFl : ltA ≠ lFl := by decide
@[simp] theorem lt_ltA_ne_lDh : ltA ≠ lDh := by decide
@[simp] theorem lt_ltA_ne_lDt : ltA ≠ lDt := by decide
@[simp] theorem lt_ltA_ne_lDg : ltA ≠ lDg := by decide
@[simp] theorem lt_ltA_ne_lDi : ltA ≠ lDi := by decide
@[simp] theorem lt_ltA_ne_lRp : ltA ≠ lRp := by decide
@[simp] theorem lt_ltA_ne_lRn : ltA ≠ lRn := by decide
@[simp] theorem lt_ltA_ne_lFle : ltA ≠ lFle := by decide
@[simp] theorem lt_ltA_ne_lDir : ltA ≠ lDir := by decide
@[simp] theorem lt_ltH_ne_ltA : ltH ≠ ltA := by decide
@[simp] theorem lt_ltH_ne_ltB : ltH ≠ ltB := by decide
@[simp] theorem lt_ltH_ne_ltD : ltH ≠ ltD := by decide
@[simp] theorem lt_ltH_ne_ltO : ltH ≠ ltO := by decide
@[simp] theorem lt_ltH_ne_ltR : ltH ≠ ltR := by decide
@[simp] theorem lt_ltH_ne_lKb : ltH ≠ lKb := by decide
@[simp] theorem lt_ltH_ne_kFu : ltH ≠ kFu := by decide
@[simp] theorem lt_ltH_ne_kD : ltH ≠ kD := by decide
@[simp] theorem lt_ltH_ne_ibT1 : ltH ≠ ibT1 := by decide
@[simp] theorem lt_ltH_ne_ibV1 : ltH ≠ ibV1 := by decide
@[simp] theorem lt_ltH_ne_ibB1 : ltH ≠ ibB1 := by decide
@[simp] theorem lt_ltH_ne_lFl : ltH ≠ lFl := by decide
@[simp] theorem lt_ltH_ne_lDh : ltH ≠ lDh := by decide
@[simp] theorem lt_ltH_ne_lDt : ltH ≠ lDt := by decide
@[simp] theorem lt_ltH_ne_lDg : ltH ≠ lDg := by decide
@[simp] theorem lt_ltH_ne_lDi : ltH ≠ lDi := by decide
@[simp] theorem lt_ltH_ne_lRp : ltH ≠ lRp := by decide
@[simp] theorem lt_ltH_ne_lRn : ltH ≠ lRn := by decide
@[simp] theorem lt_ltH_ne_lFle : ltH ≠ lFle := by decide
@[simp] theorem lt_ltH_ne_lDir : ltH ≠ lDir := by decide
@[simp] theorem lt_ltB_ne_ltA : ltB ≠ ltA := by decide
@[simp] theorem lt_ltB_ne_ltH : ltB ≠ ltH := by decide
@[simp] theorem lt_ltB_ne_ltD : ltB ≠ ltD := by decide
@[simp] theorem lt_ltB_ne_ltO : ltB ≠ ltO := by decide
@[simp] theorem lt_ltB_ne_ltR : ltB ≠ ltR := by decide
@[simp] theorem lt_ltB_ne_lKb : ltB ≠ lKb := by decide
@[simp] theorem lt_ltB_ne_kFu : ltB ≠ kFu := by decide
@[simp] theorem lt_ltB_ne_kD : ltB ≠ kD := by decide
@[simp] theorem lt_ltB_ne_ibT1 : ltB ≠ ibT1 := by decide
@[simp] theorem lt_ltB_ne_ibV1 : ltB ≠ ibV1 := by decide
@[simp] theorem lt_ltB_ne_ibB1 : ltB ≠ ibB1 := by decide
@[simp] theorem lt_ltB_ne_lFl : ltB ≠ lFl := by decide
@[simp] theorem lt_ltB_ne_lDh : ltB ≠ lDh := by decide
@[simp] theorem lt_ltB_ne_lDt : ltB ≠ lDt := by decide
@[simp] theorem lt_ltB_ne_lDg : ltB ≠ lDg := by decide
@[simp] theorem lt_ltB_ne_lDi : ltB ≠ lDi := by decide
@[simp] theorem lt_ltB_ne_lRp : ltB ≠ lRp := by decide
@[simp] theorem lt_ltB_ne_lRn : ltB ≠ lRn := by decide
@[simp] theorem lt_ltB_ne_lFle : ltB ≠ lFle := by decide
@[simp] theorem lt_ltB_ne_lDir : ltB ≠ lDir := by decide
@[simp] theorem lt_ltD_ne_ltA : ltD ≠ ltA := by decide
@[simp] theorem lt_ltD_ne_ltH : ltD ≠ ltH := by decide
@[simp] theorem lt_ltD_ne_ltB : ltD ≠ ltB := by decide
@[simp] theorem lt_ltD_ne_ltO : ltD ≠ ltO := by decide
@[simp] theorem lt_ltD_ne_ltR : ltD ≠ ltR := by decide
@[simp] theorem lt_ltD_ne_lKb : ltD ≠ lKb := by decide
@[simp] theorem lt_ltD_ne_kFu : ltD ≠ kFu := by decide
@[simp] theorem lt_ltD_ne_kD : ltD ≠ kD := by decide
@[simp] theorem lt_ltD_ne_ibT1 : ltD ≠ ibT1 := by decide
@[simp] theorem lt_ltD_ne_ibV1 : ltD ≠ ibV1 := by decide
@[simp] theorem lt_ltD_ne_ibB1 : ltD ≠ ibB1 := by decide
@[simp] theorem lt_ltD_ne_lFl : ltD ≠ lFl := by decide
@[simp] theorem lt_ltD_ne_lDh : ltD ≠ lDh := by decide
@[simp] theorem lt_ltD_ne_lDt : ltD ≠ lDt := by decide
@[simp] theorem lt_ltD_ne_lDg : ltD ≠ lDg := by decide
@[simp] theorem lt_ltD_ne_lDi : ltD ≠ lDi := by decide
@[simp] theorem lt_ltD_ne_lRp : ltD ≠ lRp := by decide
@[simp] theorem lt_ltD_ne_lRn : ltD ≠ lRn := by decide
@[simp] theorem lt_ltD_ne_lFle : ltD ≠ lFle := by decide
@[simp] theorem lt_ltD_ne_lDir : ltD ≠ lDir := by decide
@[simp] theorem lt_ltO_ne_ltA : ltO ≠ ltA := by decide
@[simp] theorem lt_ltO_ne_ltH : ltO ≠ ltH := by decide
@[simp] theorem lt_ltO_ne_ltB : ltO ≠ ltB := by decide
@[simp] theorem lt_ltO_ne_ltD : ltO ≠ ltD := by decide
@[simp] theorem lt_ltO_ne_ltR : ltO ≠ ltR := by decide
@[simp] theorem lt_ltO_ne_lKb : ltO ≠ lKb := by decide
@[simp] theorem lt_ltO_ne_kFu : ltO ≠ kFu := by decide
@[simp] theorem lt_ltO_ne_kD : ltO ≠ kD := by decide
@[simp] theorem lt_ltO_ne_ibT1 : ltO ≠ ibT1 := by decide
@[simp] theorem lt_ltO_ne_ibV1 : ltO ≠ ibV1 := by decide
@[simp] theorem lt_ltO_ne_ibB1 : ltO ≠ ibB1 := by decide
@[simp] theorem lt_ltO_ne_lFl : ltO ≠ lFl := by decide
@[simp] theorem lt_ltO_ne_lDh : ltO ≠ lDh := by decide
@[simp] theorem lt_ltO_ne_lDt : ltO ≠ lDt := by decide
@[simp] theorem lt_ltO_ne_lDg : ltO ≠ lDg := by decide
@[simp] theorem lt_ltO_ne_lDi : ltO ≠ lDi := by decide
@[simp] theorem lt_ltO_ne_lRp : ltO ≠ lRp := by decide
@[simp] theorem lt_ltO_ne_lRn : ltO ≠ lRn := by decide
@[simp] theorem lt_ltO_ne_lFle : ltO ≠ lFle := by decide
@[simp] theorem lt_ltO_ne_lDir : ltO ≠ lDir := by decide
@[simp] theorem lt_ltR_ne_ltA : ltR ≠ ltA := by decide
@[simp] theorem lt_ltR_ne_ltH : ltR ≠ ltH := by decide
@[simp] theorem lt_ltR_ne_ltB : ltR ≠ ltB := by decide
@[simp] theorem lt_ltR_ne_ltD : ltR ≠ ltD := by decide
@[simp] theorem lt_ltR_ne_ltO : ltR ≠ ltO := by decide
@[simp] theorem lt_ltR_ne_lKb : ltR ≠ lKb := by decide
@[simp] theorem lt_ltR_ne_kFu : ltR ≠ kFu := by decide
@[simp] theorem lt_ltR_ne_kD : ltR ≠ kD := by decide
@[simp] theorem lt_ltR_ne_ibT1 : ltR ≠ ibT1 := by decide
@[simp] theorem lt_ltR_ne_ibV1 : ltR ≠ ibV1 := by decide
@[simp] theorem lt_ltR_ne_ibB1 : ltR ≠ ibB1 := by decide
@[simp] theorem lt_ltR_ne_lFl : ltR ≠ lFl := by decide
@[simp] theorem lt_ltR_ne_lDh : ltR ≠ lDh := by decide
@[simp] theorem lt_ltR_ne_lDt : ltR ≠ lDt := by decide
@[simp] theorem lt_ltR_ne_lDg : ltR ≠ lDg := by decide
@[simp] theorem lt_ltR_ne_lDi : ltR ≠ lDi := by decide
@[simp] theorem lt_ltR_ne_lRp : ltR ≠ lRp := by decide
@[simp] theorem lt_ltR_ne_lRn : ltR ≠ lRn := by decide
@[simp] theorem lt_ltR_ne_lFle : ltR ≠ lFle := by decide
@[simp] theorem lt_ltR_ne_lDir : ltR ≠ lDir := by decide
@[simp] theorem lt_lKb_ne_ltA : lKb ≠ ltA := by decide
@[simp] theorem lt_lKb_ne_ltH : lKb ≠ ltH := by decide
@[simp] theorem lt_lKb_ne_ltB : lKb ≠ ltB := by decide
@[simp] theorem lt_lKb_ne_ltD : lKb ≠ ltD := by decide
@[simp] theorem lt_lKb_ne_ltO : lKb ≠ ltO := by decide
@[simp] theorem lt_lKb_ne_ltR : lKb ≠ ltR := by decide
@[simp] theorem lt_kFu_ne_ltA : kFu ≠ ltA := by decide
@[simp] theorem lt_kFu_ne_ltH : kFu ≠ ltH := by decide
@[simp] theorem lt_kFu_ne_ltB : kFu ≠ ltB := by decide
@[simp] theorem lt_kFu_ne_ltD : kFu ≠ ltD := by decide
@[simp] theorem lt_kFu_ne_ltO : kFu ≠ ltO := by decide
@[simp] theorem lt_kFu_ne_ltR : kFu ≠ ltR := by decide
@[simp] theorem lt_kD_ne_ltA : kD ≠ ltA := by decide
@[simp] theorem lt_kD_ne_ltH : kD ≠ ltH := by decide
@[simp] theorem lt_kD_ne_ltB : kD ≠ ltB := by decide
@[simp] theorem lt_kD_ne_ltD : kD ≠ ltD := by decide
@[simp] theorem lt_kD_ne_ltO : kD ≠ ltO := by decide
@[simp] theorem lt_kD_ne_ltR : kD ≠ ltR := by decide
@[simp] theorem lt_ibT1_ne_ltA : ibT1 ≠ ltA := by decide
@[simp] theorem lt_ibT1_ne_ltH : ibT1 ≠ ltH := by decide
@[simp] theorem lt_ibT1_ne_ltB : ibT1 ≠ ltB := by decide
@[simp] theorem lt_ibT1_ne_ltD : ibT1 ≠ ltD := by decide
@[simp] theorem lt_ibT1_ne_ltO : ibT1 ≠ ltO := by decide
@[simp] theorem lt_ibT1_ne_ltR : ibT1 ≠ ltR := by decide
@[simp] theorem lt_ibV1_ne_ltA : ibV1 ≠ ltA := by decide
@[simp] theorem lt_ibV1_ne_ltH : ibV1 ≠ ltH := by decide
@[simp] theorem lt_ibV1_ne_ltB : ibV1 ≠ ltB := by decide
@[simp] theorem lt_ibV1_ne_ltD : ibV1 ≠ ltD := by decide
@[simp] theorem lt_ibV1_ne_ltO : ibV1 ≠ ltO := by decide
@[simp] theorem lt_ibV1_ne_ltR : ibV1 ≠ ltR := by decide
@[simp] theorem lt_ibB1_ne_ltA : ibB1 ≠ ltA := by decide
@[simp] theorem lt_ibB1_ne_ltH : ibB1 ≠ ltH := by decide
@[simp] theorem lt_ibB1_ne_ltB : ibB1 ≠ ltB := by decide
@[simp] theorem lt_ibB1_ne_ltD : ibB1 ≠ ltD := by decide
@[simp] theorem lt_ibB1_ne_ltO : ibB1 ≠ ltO := by decide
@[simp] theorem lt_ibB1_ne_ltR : ibB1 ≠ ltR := by decide
@[simp] theorem lt_lFl_ne_ltA : lFl ≠ ltA := by decide
@[simp] theorem lt_lFl_ne_ltH : lFl ≠ ltH := by decide
@[simp] theorem lt_lFl_ne_ltB : lFl ≠ ltB := by decide
@[simp] theorem lt_lFl_ne_ltD : lFl ≠ ltD := by decide
@[simp] theorem lt_lFl_ne_ltO : lFl ≠ ltO := by decide
@[simp] theorem lt_lFl_ne_ltR : lFl ≠ ltR := by decide
@[simp] theorem lt_lDh_ne_ltA : lDh ≠ ltA := by decide
@[simp] theorem lt_lDh_ne_ltH : lDh ≠ ltH := by decide
@[simp] theorem lt_lDh_ne_ltB : lDh ≠ ltB := by decide
@[simp] theorem lt_lDh_ne_ltD : lDh ≠ ltD := by decide
@[simp] theorem lt_lDh_ne_ltO : lDh ≠ ltO := by decide
@[simp] theorem lt_lDh_ne_ltR : lDh ≠ ltR := by decide
@[simp] theorem lt_lDt_ne_ltA : lDt ≠ ltA := by decide
@[simp] theorem lt_lDt_ne_ltH : lDt ≠ ltH := by decide
@[simp] theorem lt_lDt_ne_ltB : lDt ≠ ltB := by decide
@[simp] theorem lt_lDt_ne_ltD : lDt ≠ ltD := by decide
@[simp] theorem lt_lDt_ne_ltO : lDt ≠ ltO := by decide
@[simp] theorem lt_lDt_ne_ltR : lDt ≠ ltR := by decide
@[simp] theorem lt_lDg_ne_ltA : lDg ≠ ltA := by decide
@[simp] theorem lt_lDg_ne_ltH : lDg ≠ ltH := by decide
@[simp] theorem lt_lDg_ne_ltB : lDg ≠ ltB := by decide
@[simp] theorem lt_lDg_ne_ltD : lDg ≠ ltD := by decide
@[simp] theorem lt_lDg_ne_ltO : lDg ≠ ltO := by decide
@[simp] theorem lt_lDg_ne_ltR : lDg ≠ ltR := by decide
@[simp] theorem lt_lDi_ne_ltA : lDi ≠ ltA := by decide
@[simp] theorem lt_lDi_ne_ltH : lDi ≠ ltH := by decide
@[simp] theorem lt_lDi_ne_ltB : lDi ≠ ltB := by decide
@[simp] theorem lt_lDi_ne_ltD : lDi ≠ ltD := by decide
@[simp] theorem lt_lDi_ne_ltO : lDi ≠ ltO := by decide
@[simp] theorem lt_lDi_ne_ltR : lDi ≠ ltR := by decide
@[simp] theorem lt_lRp_ne_ltA : lRp ≠ ltA := by decide
@[simp] theorem lt_lRp_ne_ltH : lRp ≠ ltH := by decide
@[simp] theorem lt_lRp_ne_ltB : lRp ≠ ltB := by decide
@[simp] theorem lt_lRp_ne_ltD : lRp ≠ ltD := by decide
@[simp] theorem lt_lRp_ne_ltO : lRp ≠ ltO := by decide
@[simp] theorem lt_lRp_ne_ltR : lRp ≠ ltR := by decide
@[simp] theorem lt_lRn_ne_ltA : lRn ≠ ltA := by decide
@[simp] theorem lt_lRn_ne_ltH : lRn ≠ ltH := by decide
@[simp] theorem lt_lRn_ne_ltB : lRn ≠ ltB := by decide
@[simp] theorem lt_lRn_ne_ltD : lRn ≠ ltD := by decide
@[simp] theorem lt_lRn_ne_ltO : lRn ≠ ltO := by decide
@[simp] theorem lt_lRn_ne_ltR : lRn ≠ ltR := by decide
@[simp] theorem lt_lFle_ne_ltA : lFle ≠ ltA := by decide
@[simp] theorem lt_lFle_ne_ltH : lFle ≠ ltH := by decide
@[simp] theorem lt_lFle_ne_ltB : lFle ≠ ltB := by decide
@[simp] theorem lt_lFle_ne_ltD : lFle ≠ ltD := by decide
@[simp] theorem lt_lFle_ne_ltO : lFle ≠ ltO := by decide
@[simp] theorem lt_lFle_ne_ltR : lFle ≠ ltR := by decide
@[simp] theorem lt_lDir_ne_ltA : lDir ≠ ltA := by decide
@[simp] theorem lt_lDir_ne_ltH : lDir ≠ ltH := by decide
@[simp] theorem lt_lDir_ne_ltB : lDir ≠ ltB := by decide
@[simp] theorem lt_lDir_ne_ltD : lDir ≠ ltD := by decide
@[simp] theorem lt_lDir_ne_ltO : lDir ≠ ltO := by decide
@[simp] theorem lt_lDir_ne_ltR : lDir ≠ ltR := by decide

def ltLocals : List MlS := [ltA, ltH, lFl, lDh, lDt, lDg, lDi, lRp, lRn, ltB, ltD, ltO, ltR]

def ltCore : ProgHOL 64 :=
  .seq (.call (some (some (.local, ltA), none)) fI [vv kFu, vv kD, vv ibT1])
  (.seq (.call (some (some (.local, ltH), none)) fW [vv kFu, vv kD, vv ltA])
  (.ite (tagIsE ltH 2)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ltH)) (.seq eViewP
    (.seq (.call (some (some (.local, ltB), none)) fI [vv kFu, vv kD, vv ibV1])
    (.seq (.call (some (some (.local, ltD), none)) fD [vv kFu, vv kD, vv ltB, vv ibT1])
    (.ite (.cmp .equal (vv ltD) (.const 0)) hang
    (.seq (.call (some (some (.local, ltO), none)) ExI.fInst1F
        [.const (BitVec.ofNat 64 coreWalkFuel), vv ibB1, vv ibV1, .const 0])
    (.seq (.call (some (some (.local, ltR), none)) fI [vv kFu, vv kD, vv ltO]) (.return (vv ltR))))))))))
    hang))

def ltBody : ProgHOL 64 := prologue ltLocals ltCore

section
variable {σ : Type}

theorem is_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ isLocals → (ctxEnv C ++ ibsParams.zip vals).get x = none :=
  Knot.params_none C isLocals ibsParams vals (by decide) (by decide)

theorem is_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (hct : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)) (s : AState) (u : LIdx) :
    SpecR (σ := σ) (Pre C s (ibsParams.zip [Enc.idxW u])) isBody s (ibSortT u) (PostK C) := by
  refine specR_prologue (postK_locals C) (is_none C _) ?_
  unfold ibSortT
  refine callLN isS fInternLSucc [lEu] [vv ibU] internLSuccBody [Enc.idxW u] (by decide) rfl (by decide) hcs
    ⟨by simp +decide [Env.get, ibsParams, ctxEnv], trivial⟩ (.succ u) (internLSucc_body_spec ra C hok s u)
    (fun su s1 _ => ?_)
  refine specR_bindPure ?_
  refine ILP.callE_spec isR fInternSort [lEu] [vv isS] sortBody [Enc.idxW su] (by decide) rfl (by decide) hct
    ⟨by simp, trivial⟩ (sort_body_spec ra C hok s1 su) (fun r s2 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ik_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ikLocals → (ctxEnv C ++ ibcParams.zip vals).get x = none :=
  Knot.params_none C ikLocals ibcParams vals (by decide) (by decide)

theorem ik_spec (C : Ctx) (hok : CtxOK C)
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hct : C.code.lookup CT.fCT = some (CV.cvParams.map (fun p => (p, ShapeHOL.one)), CT.ctBody C, .one))
    (s : AState) (c : NIdx) (us : LsIdx)
    (hCt : ∀ ci o ok, C.fe.find? c = some ci → CIE C.EB C.EH o ci →
      EBlk C.EH ok (ci.toConstantVal.levelParams.map Enc.idxW) →
      SpecR (σ := σ) (Pre C s (CV.cvParams.zip [Enc.idxW ci.toConstantVal.name, ecell C ok,
        Enc.idxW ci.toConstantVal.type, Enc.idxW us])) (CT.ctBody C) s (constTyAt ci.toConstantVal us) (PostK C)) :
    SpecR (σ := σ) (Pre C s (ibcParams.zip [Enc.idxW c, Enc.idxW us])) (ikBody C) s (ibConstT C.fe c us) (PostK C) := by
  refine specR_prologue (postK_locals C) (ik_none C _) ?_
  unfold ikCore ibConstT
  refine specR_envFindI hok hmg hmp ikW (vv ibN) c (by decide)
    (by simp +decide [Env.get, ibcParams, ctxEnv]) (by simp +decide [Env.get, ibcParams, ctxEnv]) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ikQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  have hcv := hci.1
  obtain ⟨hnm, ⟨w, hw, ok, hw', hblk⟩, hty⟩ := id hcv
  subst hw'
  refine specR_envLoadI ikLp (.op .add [vv ikQ, .const 16]) (o + 2) _ (by decide)
    (by simp [sev, vv]; exact UD.ecell_add16 C o) (by simpa using hw) ?_
  have hl0 : C.EH[ok]? = some (BitVec.ofNat 64 ci.toConstantVal.levelParams.length) := by
    have := hblk.1; simpa using this
  refine specR_envLoadI ikLl (vv ikLp) ok _ (by decide) (by simp; rfl) hl0 ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ibcParams, ctxEnv]) ?_
  refine specR_assignI lDh (vv ibUs) (Enc.idxW us) (by decide) (by simp +decide [Env.get, ibcParams, ctxEnv]) ?_
  refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, ibcParams, ctxEnv]) (by decide)
    (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLs_run us s vl hvl) ?_
  try dsimp only
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  have hlp : ci.toConstantVal.levelParams.length < 2 ^ 61 := by
    have := eblk_small hok ht.sr (show EBlk C.EH ok (ci.toConstantVal.levelParams.map Enc.idxW) from hblk)
    simpa using this
  by_cases hl : vl.length = ci.toConstantVal.levelParams.length
  · rw [if_neg (by simpa using hl)]
    refine specR_ifI _ 0 (by simp [sev, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_envLoadI ikNm (.op .add [vv ikQ, .const 8]) (o + 1) _ (by decide)
      (by simp [sev, vv]; exact ecell_add8 C o) hnm ?_
    refine specR_envLoadI ikTy (.op .add [vv ikQ, .const 24]) (o + 3) _ (by decide)
      (by simp [sev, vv]; exact ecell_add24 C o) (by simpa using hty) ?_
    exact specR_callKR ikX CT.fCT CV.cvParams [vv ikNm, vv ikLp, vv ikTy, vv ibUs] (CT.ctBody C)
      [Enc.idxW ci.toConstantVal.name, ecell C ok, Enc.idxW ci.toConstantVal.type, Enc.idxW us] (by decide) rfl
      (by decide) hct ⟨by simp, by simp; rfl, by simp, by simp +decide [Env.get, ibcParams, ctxEnv], trivial⟩
      (hCt ci o ok hfind hci hblk)
  · rw [if_pos (by simpa using hl)]
    have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 ci.toConstantVal.levelParams.length := fun x =>
      hl ((UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp x)
    exact specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))

theorem lt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ltLocals → (ctxEnv C ++ iltParams.zip vals).get x = none :=
  Knot.params_none C ltLocals iltParams vals (by decide) (by decide)

theorem lt_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (s : AState) (d : Nat) (ty v b : EIdx)
    (hI : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (iltParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW v,
      Enc.idxW b])) ltBody s (ibLetT (knot mode C n) C.fe d ty v b) (PostK C) := by
  refine specR_prologue (postK_locals C) (lt_none C _) ?_
  unfold ltCore ibLetT ensureSort
  simp only [bind_assoc]
  refine Big.specR_callKC ltA fI kParams [vv kFu, vv kD, vv ibT1] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv],
      by simp +decide [Env.get, iltParams, ctxEnv], trivial⟩ (hI C.H s (List.prefix_refl _) ty)
    (fun tty s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) ltH fW kParams [vv kFu, vv kD, vv ltA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tty] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], by simp, trivial⟩
    (hW H1 s1 hp1 tty) (fun hh s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine Knot.specR_tagIteV ltH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ltH) (Enc.idxW hh) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    simp only [bind_assoc]
    refine specR_congr (view_bind_eq hh vw _ s2 hv) ?_
    have h2 : vw.tagN = 2 := by rw [htn, htg]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
    simp only [pure_bind]
    refine specR_dropM ?_
    refine Big.specR_callKC (C := ctxH C H2) ltB fI kParams [vv kFu, vv kD, vv ibV1] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW v] (by decide) rfl (by decide) hci
      ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv],
        by simp +decide [Env.get, iltParams, ctxEnv], trivial⟩ (hI H2 s2 hp12 v) (fun tv s3 H3 hp3 _ => ?_)
    have hp13 : C.H <+: H3 := hp12.trans hp3
    refine specR_callNIH (C := ctxH C H3) ltD fD dParams [vv kFu, vv kD, vv ltB, vv ibT1] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tv, Enc.idxW ty] (by decide) rfl (by decide) hcd
      ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], by simp,
        by simp +decide [Env.get, iltParams, ctxEnv], trivial⟩
      (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H3 s3 hp13 tv ty u hu (fun i hi _ => hlk i (by omega)))
      (fun df w s4 H4 hp4 hw => ?_)
    subst hw
    have hp14 : C.H <+: H4 := hp13.trans hp4
    cases df
    · simp only [Bool.not_false, ↓reduceIte]
      exact specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine ILP.callE_spec (C := ctxH C H4) ltO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ibB1, vv ibV1, .const 0] (ExI.fastBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW v, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
      ⟨rfl, by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], rfl, trivial⟩
      (ExI.fast_spec ra (ctxH C H4) (ctxOK_H hok H4) (ExIS.codes_H C H4 hcI') s4 coreWalkFuel b v 0
        CV.coreWalkFuel_lt (by decide)) (fun ob s5 => ?_)
    refine specR_bindPure ?_
    refine Big.specR_callKC (C := ctxH C H4) ltR fI kParams [vv kFu, vv kD, vv ltO] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ob] (by decide) rfl (by decide) hci
      ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], by simp, trivial⟩
      (hI H4 s5 hp14 ob) (fun r s6 H5 hp5 _ => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H5, hp14.trans hp5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_hangI

end

end ConPanqueque.T.WC
