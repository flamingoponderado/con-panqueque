import ConPanqueque.T.Big.Limbs
import ConPanqueque.T.Knot
import ConPanqueque.T.NView
import ConPanqueque.T.Copy
import ConPanqueque.T.InstLP
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Comparing two `Nat` literals

`bigCmp(a, b)` on two literal handles answers `0`, `1` or `2` for `<`, `=`, `>`: by limb count, then a
running verdict over the limbs from the top (the loop has no early exit, so it is a counted loop).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def cmpN (x y : Nat) : Nat := if x < y then 0 else if x = y then 1 else 2

def bA := ofString "ba"
def bB := ofString "bb"
def bPa := ofString "bpa"
def bLa := ofString "bla"
def bQa := ofString "bqa"
def bQb := ofString "bqb"
def bX := ofString "bx"
def bY := ofString "by"
def bR := ofString "br"
def bI := ofString "bi"

@[simp] theorem bA_ne_bB : bA ≠ bB := by decide
@[simp] theorem bA_ne_bPa : bA ≠ bPa := by decide
@[simp] theorem bA_ne_bLa : bA ≠ bLa := by decide
@[simp] theorem bA_ne_bQa : bA ≠ bQa := by decide
@[simp] theorem bA_ne_bQb : bA ≠ bQb := by decide
@[simp] theorem bA_ne_bX : bA ≠ bX := by decide
@[simp] theorem bA_ne_bY : bA ≠ bY := by decide
@[simp] theorem bA_ne_bR : bA ≠ bR := by decide
@[simp] theorem bA_ne_bI : bA ≠ bI := by decide
@[simp] theorem bB_ne_bA : bB ≠ bA := by decide
@[simp] theorem bB_ne_bPa : bB ≠ bPa := by decide
@[simp] theorem bB_ne_bLa : bB ≠ bLa := by decide
@[simp] theorem bB_ne_bQa : bB ≠ bQa := by decide
@[simp] theorem bB_ne_bQb : bB ≠ bQb := by decide
@[simp] theorem bB_ne_bX : bB ≠ bX := by decide
@[simp] theorem bB_ne_bY : bB ≠ bY := by decide
@[simp] theorem bB_ne_bR : bB ≠ bR := by decide
@[simp] theorem bB_ne_bI : bB ≠ bI := by decide
@[simp] theorem bPa_ne_bA : bPa ≠ bA := by decide
@[simp] theorem bPa_ne_bB : bPa ≠ bB := by decide
@[simp] theorem bPa_ne_bLa : bPa ≠ bLa := by decide
@[simp] theorem bPa_ne_bQa : bPa ≠ bQa := by decide
@[simp] theorem bPa_ne_bQb : bPa ≠ bQb := by decide
@[simp] theorem bPa_ne_bX : bPa ≠ bX := by decide
@[simp] theorem bPa_ne_bY : bPa ≠ bY := by decide
@[simp] theorem bPa_ne_bR : bPa ≠ bR := by decide
@[simp] theorem bPa_ne_bI : bPa ≠ bI := by decide
@[simp] theorem bLa_ne_bA : bLa ≠ bA := by decide
@[simp] theorem bLa_ne_bB : bLa ≠ bB := by decide
@[simp] theorem bLa_ne_bPa : bLa ≠ bPa := by decide
@[simp] theorem bLa_ne_bQa : bLa ≠ bQa := by decide
@[simp] theorem bLa_ne_bQb : bLa ≠ bQb := by decide
@[simp] theorem bLa_ne_bX : bLa ≠ bX := by decide
@[simp] theorem bLa_ne_bY : bLa ≠ bY := by decide
@[simp] theorem bLa_ne_bR : bLa ≠ bR := by decide
@[simp] theorem bLa_ne_bI : bLa ≠ bI := by decide
@[simp] theorem bQa_ne_bA : bQa ≠ bA := by decide
@[simp] theorem bQa_ne_bB : bQa ≠ bB := by decide
@[simp] theorem bQa_ne_bPa : bQa ≠ bPa := by decide
@[simp] theorem bQa_ne_bLa : bQa ≠ bLa := by decide
@[simp] theorem bQa_ne_bQb : bQa ≠ bQb := by decide
@[simp] theorem bQa_ne_bX : bQa ≠ bX := by decide
@[simp] theorem bQa_ne_bY : bQa ≠ bY := by decide
@[simp] theorem bQa_ne_bR : bQa ≠ bR := by decide
@[simp] theorem bQa_ne_bI : bQa ≠ bI := by decide
@[simp] theorem bQb_ne_bA : bQb ≠ bA := by decide
@[simp] theorem bQb_ne_bB : bQb ≠ bB := by decide
@[simp] theorem bQb_ne_bPa : bQb ≠ bPa := by decide
@[simp] theorem bQb_ne_bLa : bQb ≠ bLa := by decide
@[simp] theorem bQb_ne_bQa : bQb ≠ bQa := by decide
@[simp] theorem bQb_ne_bX : bQb ≠ bX := by decide
@[simp] theorem bQb_ne_bY : bQb ≠ bY := by decide
@[simp] theorem bQb_ne_bR : bQb ≠ bR := by decide
@[simp] theorem bQb_ne_bI : bQb ≠ bI := by decide
@[simp] theorem bX_ne_bA : bX ≠ bA := by decide
@[simp] theorem bX_ne_bB : bX ≠ bB := by decide
@[simp] theorem bX_ne_bPa : bX ≠ bPa := by decide
@[simp] theorem bX_ne_bLa : bX ≠ bLa := by decide
@[simp] theorem bX_ne_bQa : bX ≠ bQa := by decide
@[simp] theorem bX_ne_bQb : bX ≠ bQb := by decide
@[simp] theorem bX_ne_bY : bX ≠ bY := by decide
@[simp] theorem bX_ne_bR : bX ≠ bR := by decide
@[simp] theorem bX_ne_bI : bX ≠ bI := by decide
@[simp] theorem bY_ne_bA : bY ≠ bA := by decide
@[simp] theorem bY_ne_bB : bY ≠ bB := by decide
@[simp] theorem bY_ne_bPa : bY ≠ bPa := by decide
@[simp] theorem bY_ne_bLa : bY ≠ bLa := by decide
@[simp] theorem bY_ne_bQa : bY ≠ bQa := by decide
@[simp] theorem bY_ne_bQb : bY ≠ bQb := by decide
@[simp] theorem bY_ne_bX : bY ≠ bX := by decide
@[simp] theorem bY_ne_bR : bY ≠ bR := by decide
@[simp] theorem bY_ne_bI : bY ≠ bI := by decide
@[simp] theorem bR_ne_bA : bR ≠ bA := by decide
@[simp] theorem bR_ne_bB : bR ≠ bB := by decide
@[simp] theorem bR_ne_bPa : bR ≠ bPa := by decide
@[simp] theorem bR_ne_bLa : bR ≠ bLa := by decide
@[simp] theorem bR_ne_bQa : bR ≠ bQa := by decide
@[simp] theorem bR_ne_bQb : bR ≠ bQb := by decide
@[simp] theorem bR_ne_bX : bR ≠ bX := by decide
@[simp] theorem bR_ne_bY : bR ≠ bY := by decide
@[simp] theorem bR_ne_bI : bR ≠ bI := by decide
@[simp] theorem bI_ne_bA : bI ≠ bA := by decide
@[simp] theorem bI_ne_bB : bI ≠ bB := by decide
@[simp] theorem bI_ne_bPa : bI ≠ bPa := by decide
@[simp] theorem bI_ne_bLa : bI ≠ bLa := by decide
@[simp] theorem bI_ne_bQa : bI ≠ bQa := by decide
@[simp] theorem bI_ne_bQb : bI ≠ bQb := by decide
@[simp] theorem bI_ne_bX : bI ≠ bX := by decide
@[simp] theorem bI_ne_bY : bI ≠ bY := by decide
@[simp] theorem bI_ne_bR : bI ≠ bR := by decide

@[simp] theorem bA_ne_lFl : bA ≠ lFl := by decide
@[simp] theorem lFl_ne_bA : lFl ≠ bA := by decide
@[simp] theorem bA_ne_lDh : bA ≠ lDh := by decide
@[simp] theorem lDh_ne_bA : lDh ≠ bA := by decide
@[simp] theorem bA_ne_lDt : bA ≠ lDt := by decide
@[simp] theorem lDt_ne_bA : lDt ≠ bA := by decide
@[simp] theorem bA_ne_lDg : bA ≠ lDg := by decide
@[simp] theorem lDg_ne_bA : lDg ≠ bA := by decide
@[simp] theorem bA_ne_lDi : bA ≠ lDi := by decide
@[simp] theorem lDi_ne_bA : lDi ≠ bA := by decide
@[simp] theorem bA_ne_lRp : bA ≠ lRp := by decide
@[simp] theorem lRp_ne_bA : lRp ≠ bA := by decide
@[simp] theorem bA_ne_lRn : bA ≠ lRn := by decide
@[simp] theorem lRn_ne_bA : lRn ≠ bA := by decide
@[simp] theorem bA_ne_lFle : bA ≠ lFle := by decide
@[simp] theorem lFle_ne_bA : lFle ≠ bA := by decide
@[simp] theorem bA_ne_lDir : bA ≠ lDir := by decide
@[simp] theorem lDir_ne_bA : lDir ≠ bA := by decide
@[simp] theorem bA_ne_lFln : bA ≠ lFln := by decide
@[simp] theorem lFln_ne_bA : lFln ≠ bA := by decide
@[simp] theorem bA_ne_lFll : bA ≠ lFll := by decide
@[simp] theorem lFll_ne_bA : lFll ≠ bA := by decide
@[simp] theorem bA_ne_lFls : bA ≠ lFls := by decide
@[simp] theorem lFls_ne_bA : lFls ≠ bA := by decide
@[simp] theorem bA_ne_lKb : bA ≠ lKb := by decide
@[simp] theorem lKb_ne_bA : lKb ≠ bA := by decide
@[simp] theorem bB_ne_lFl : bB ≠ lFl := by decide
@[simp] theorem lFl_ne_bB : lFl ≠ bB := by decide
@[simp] theorem bB_ne_lDh : bB ≠ lDh := by decide
@[simp] theorem lDh_ne_bB : lDh ≠ bB := by decide
@[simp] theorem bB_ne_lDt : bB ≠ lDt := by decide
@[simp] theorem lDt_ne_bB : lDt ≠ bB := by decide
@[simp] theorem bB_ne_lDg : bB ≠ lDg := by decide
@[simp] theorem lDg_ne_bB : lDg ≠ bB := by decide
@[simp] theorem bB_ne_lDi : bB ≠ lDi := by decide
@[simp] theorem lDi_ne_bB : lDi ≠ bB := by decide
@[simp] theorem bB_ne_lRp : bB ≠ lRp := by decide
@[simp] theorem lRp_ne_bB : lRp ≠ bB := by decide
@[simp] theorem bB_ne_lRn : bB ≠ lRn := by decide
@[simp] theorem lRn_ne_bB : lRn ≠ bB := by decide
@[simp] theorem bB_ne_lFle : bB ≠ lFle := by decide
@[simp] theorem lFle_ne_bB : lFle ≠ bB := by decide
@[simp] theorem bB_ne_lDir : bB ≠ lDir := by decide
@[simp] theorem lDir_ne_bB : lDir ≠ bB := by decide
@[simp] theorem bB_ne_lFln : bB ≠ lFln := by decide
@[simp] theorem lFln_ne_bB : lFln ≠ bB := by decide
@[simp] theorem bB_ne_lFll : bB ≠ lFll := by decide
@[simp] theorem lFll_ne_bB : lFll ≠ bB := by decide
@[simp] theorem bB_ne_lFls : bB ≠ lFls := by decide
@[simp] theorem lFls_ne_bB : lFls ≠ bB := by decide
@[simp] theorem bB_ne_lKb : bB ≠ lKb := by decide
@[simp] theorem lKb_ne_bB : lKb ≠ bB := by decide
@[simp] theorem bPa_ne_lFl : bPa ≠ lFl := by decide
@[simp] theorem lFl_ne_bPa : lFl ≠ bPa := by decide
@[simp] theorem bPa_ne_lDh : bPa ≠ lDh := by decide
@[simp] theorem lDh_ne_bPa : lDh ≠ bPa := by decide
@[simp] theorem bPa_ne_lDt : bPa ≠ lDt := by decide
@[simp] theorem lDt_ne_bPa : lDt ≠ bPa := by decide
@[simp] theorem bPa_ne_lDg : bPa ≠ lDg := by decide
@[simp] theorem lDg_ne_bPa : lDg ≠ bPa := by decide
@[simp] theorem bPa_ne_lDi : bPa ≠ lDi := by decide
@[simp] theorem lDi_ne_bPa : lDi ≠ bPa := by decide
@[simp] theorem bPa_ne_lRp : bPa ≠ lRp := by decide
@[simp] theorem lRp_ne_bPa : lRp ≠ bPa := by decide
@[simp] theorem bPa_ne_lRn : bPa ≠ lRn := by decide
@[simp] theorem lRn_ne_bPa : lRn ≠ bPa := by decide
@[simp] theorem bPa_ne_lFle : bPa ≠ lFle := by decide
@[simp] theorem lFle_ne_bPa : lFle ≠ bPa := by decide
@[simp] theorem bPa_ne_lDir : bPa ≠ lDir := by decide
@[simp] theorem lDir_ne_bPa : lDir ≠ bPa := by decide
@[simp] theorem bPa_ne_lFln : bPa ≠ lFln := by decide
@[simp] theorem lFln_ne_bPa : lFln ≠ bPa := by decide
@[simp] theorem bPa_ne_lFll : bPa ≠ lFll := by decide
@[simp] theorem lFll_ne_bPa : lFll ≠ bPa := by decide
@[simp] theorem bPa_ne_lFls : bPa ≠ lFls := by decide
@[simp] theorem lFls_ne_bPa : lFls ≠ bPa := by decide
@[simp] theorem bPa_ne_lKb : bPa ≠ lKb := by decide
@[simp] theorem lKb_ne_bPa : lKb ≠ bPa := by decide
@[simp] theorem bLa_ne_lFl : bLa ≠ lFl := by decide
@[simp] theorem lFl_ne_bLa : lFl ≠ bLa := by decide
@[simp] theorem bLa_ne_lDh : bLa ≠ lDh := by decide
@[simp] theorem lDh_ne_bLa : lDh ≠ bLa := by decide
@[simp] theorem bLa_ne_lDt : bLa ≠ lDt := by decide
@[simp] theorem lDt_ne_bLa : lDt ≠ bLa := by decide
@[simp] theorem bLa_ne_lDg : bLa ≠ lDg := by decide
@[simp] theorem lDg_ne_bLa : lDg ≠ bLa := by decide
@[simp] theorem bLa_ne_lDi : bLa ≠ lDi := by decide
@[simp] theorem lDi_ne_bLa : lDi ≠ bLa := by decide
@[simp] theorem bLa_ne_lRp : bLa ≠ lRp := by decide
@[simp] theorem lRp_ne_bLa : lRp ≠ bLa := by decide
@[simp] theorem bLa_ne_lRn : bLa ≠ lRn := by decide
@[simp] theorem lRn_ne_bLa : lRn ≠ bLa := by decide
@[simp] theorem bLa_ne_lFle : bLa ≠ lFle := by decide
@[simp] theorem lFle_ne_bLa : lFle ≠ bLa := by decide
@[simp] theorem bLa_ne_lDir : bLa ≠ lDir := by decide
@[simp] theorem lDir_ne_bLa : lDir ≠ bLa := by decide
@[simp] theorem bLa_ne_lFln : bLa ≠ lFln := by decide
@[simp] theorem lFln_ne_bLa : lFln ≠ bLa := by decide
@[simp] theorem bLa_ne_lFll : bLa ≠ lFll := by decide
@[simp] theorem lFll_ne_bLa : lFll ≠ bLa := by decide
@[simp] theorem bLa_ne_lFls : bLa ≠ lFls := by decide
@[simp] theorem lFls_ne_bLa : lFls ≠ bLa := by decide
@[simp] theorem bLa_ne_lKb : bLa ≠ lKb := by decide
@[simp] theorem lKb_ne_bLa : lKb ≠ bLa := by decide
@[simp] theorem bQa_ne_lFl : bQa ≠ lFl := by decide
@[simp] theorem lFl_ne_bQa : lFl ≠ bQa := by decide
@[simp] theorem bQa_ne_lDh : bQa ≠ lDh := by decide
@[simp] theorem lDh_ne_bQa : lDh ≠ bQa := by decide
@[simp] theorem bQa_ne_lDt : bQa ≠ lDt := by decide
@[simp] theorem lDt_ne_bQa : lDt ≠ bQa := by decide
@[simp] theorem bQa_ne_lDg : bQa ≠ lDg := by decide
@[simp] theorem lDg_ne_bQa : lDg ≠ bQa := by decide
@[simp] theorem bQa_ne_lDi : bQa ≠ lDi := by decide
@[simp] theorem lDi_ne_bQa : lDi ≠ bQa := by decide
@[simp] theorem bQa_ne_lRp : bQa ≠ lRp := by decide
@[simp] theorem lRp_ne_bQa : lRp ≠ bQa := by decide
@[simp] theorem bQa_ne_lRn : bQa ≠ lRn := by decide
@[simp] theorem lRn_ne_bQa : lRn ≠ bQa := by decide
@[simp] theorem bQa_ne_lFle : bQa ≠ lFle := by decide
@[simp] theorem lFle_ne_bQa : lFle ≠ bQa := by decide
@[simp] theorem bQa_ne_lDir : bQa ≠ lDir := by decide
@[simp] theorem lDir_ne_bQa : lDir ≠ bQa := by decide
@[simp] theorem bQa_ne_lFln : bQa ≠ lFln := by decide
@[simp] theorem lFln_ne_bQa : lFln ≠ bQa := by decide
@[simp] theorem bQa_ne_lFll : bQa ≠ lFll := by decide
@[simp] theorem lFll_ne_bQa : lFll ≠ bQa := by decide
@[simp] theorem bQa_ne_lFls : bQa ≠ lFls := by decide
@[simp] theorem lFls_ne_bQa : lFls ≠ bQa := by decide
@[simp] theorem bQa_ne_lKb : bQa ≠ lKb := by decide
@[simp] theorem lKb_ne_bQa : lKb ≠ bQa := by decide
@[simp] theorem bQb_ne_lFl : bQb ≠ lFl := by decide
@[simp] theorem lFl_ne_bQb : lFl ≠ bQb := by decide
@[simp] theorem bQb_ne_lDh : bQb ≠ lDh := by decide
@[simp] theorem lDh_ne_bQb : lDh ≠ bQb := by decide
@[simp] theorem bQb_ne_lDt : bQb ≠ lDt := by decide
@[simp] theorem lDt_ne_bQb : lDt ≠ bQb := by decide
@[simp] theorem bQb_ne_lDg : bQb ≠ lDg := by decide
@[simp] theorem lDg_ne_bQb : lDg ≠ bQb := by decide
@[simp] theorem bQb_ne_lDi : bQb ≠ lDi := by decide
@[simp] theorem lDi_ne_bQb : lDi ≠ bQb := by decide
@[simp] theorem bQb_ne_lRp : bQb ≠ lRp := by decide
@[simp] theorem lRp_ne_bQb : lRp ≠ bQb := by decide
@[simp] theorem bQb_ne_lRn : bQb ≠ lRn := by decide
@[simp] theorem lRn_ne_bQb : lRn ≠ bQb := by decide
@[simp] theorem bQb_ne_lFle : bQb ≠ lFle := by decide
@[simp] theorem lFle_ne_bQb : lFle ≠ bQb := by decide
@[simp] theorem bQb_ne_lDir : bQb ≠ lDir := by decide
@[simp] theorem lDir_ne_bQb : lDir ≠ bQb := by decide
@[simp] theorem bQb_ne_lFln : bQb ≠ lFln := by decide
@[simp] theorem lFln_ne_bQb : lFln ≠ bQb := by decide
@[simp] theorem bQb_ne_lFll : bQb ≠ lFll := by decide
@[simp] theorem lFll_ne_bQb : lFll ≠ bQb := by decide
@[simp] theorem bQb_ne_lFls : bQb ≠ lFls := by decide
@[simp] theorem lFls_ne_bQb : lFls ≠ bQb := by decide
@[simp] theorem bQb_ne_lKb : bQb ≠ lKb := by decide
@[simp] theorem lKb_ne_bQb : lKb ≠ bQb := by decide
@[simp] theorem bX_ne_lFl : bX ≠ lFl := by decide
@[simp] theorem lFl_ne_bX : lFl ≠ bX := by decide
@[simp] theorem bX_ne_lDh : bX ≠ lDh := by decide
@[simp] theorem lDh_ne_bX : lDh ≠ bX := by decide
@[simp] theorem bX_ne_lDt : bX ≠ lDt := by decide
@[simp] theorem lDt_ne_bX : lDt ≠ bX := by decide
@[simp] theorem bX_ne_lDg : bX ≠ lDg := by decide
@[simp] theorem lDg_ne_bX : lDg ≠ bX := by decide
@[simp] theorem bX_ne_lDi : bX ≠ lDi := by decide
@[simp] theorem lDi_ne_bX : lDi ≠ bX := by decide
@[simp] theorem bX_ne_lRp : bX ≠ lRp := by decide
@[simp] theorem lRp_ne_bX : lRp ≠ bX := by decide
@[simp] theorem bX_ne_lRn : bX ≠ lRn := by decide
@[simp] theorem lRn_ne_bX : lRn ≠ bX := by decide
@[simp] theorem bX_ne_lFle : bX ≠ lFle := by decide
@[simp] theorem lFle_ne_bX : lFle ≠ bX := by decide
@[simp] theorem bX_ne_lDir : bX ≠ lDir := by decide
@[simp] theorem lDir_ne_bX : lDir ≠ bX := by decide
@[simp] theorem bX_ne_lFln : bX ≠ lFln := by decide
@[simp] theorem lFln_ne_bX : lFln ≠ bX := by decide
@[simp] theorem bX_ne_lFll : bX ≠ lFll := by decide
@[simp] theorem lFll_ne_bX : lFll ≠ bX := by decide
@[simp] theorem bX_ne_lFls : bX ≠ lFls := by decide
@[simp] theorem lFls_ne_bX : lFls ≠ bX := by decide
@[simp] theorem bX_ne_lKb : bX ≠ lKb := by decide
@[simp] theorem lKb_ne_bX : lKb ≠ bX := by decide
@[simp] theorem bY_ne_lFl : bY ≠ lFl := by decide
@[simp] theorem lFl_ne_bY : lFl ≠ bY := by decide
@[simp] theorem bY_ne_lDh : bY ≠ lDh := by decide
@[simp] theorem lDh_ne_bY : lDh ≠ bY := by decide
@[simp] theorem bY_ne_lDt : bY ≠ lDt := by decide
@[simp] theorem lDt_ne_bY : lDt ≠ bY := by decide
@[simp] theorem bY_ne_lDg : bY ≠ lDg := by decide
@[simp] theorem lDg_ne_bY : lDg ≠ bY := by decide
@[simp] theorem bY_ne_lDi : bY ≠ lDi := by decide
@[simp] theorem lDi_ne_bY : lDi ≠ bY := by decide
@[simp] theorem bY_ne_lRp : bY ≠ lRp := by decide
@[simp] theorem lRp_ne_bY : lRp ≠ bY := by decide
@[simp] theorem bY_ne_lRn : bY ≠ lRn := by decide
@[simp] theorem lRn_ne_bY : lRn ≠ bY := by decide
@[simp] theorem bY_ne_lFle : bY ≠ lFle := by decide
@[simp] theorem lFle_ne_bY : lFle ≠ bY := by decide
@[simp] theorem bY_ne_lDir : bY ≠ lDir := by decide
@[simp] theorem lDir_ne_bY : lDir ≠ bY := by decide
@[simp] theorem bY_ne_lFln : bY ≠ lFln := by decide
@[simp] theorem lFln_ne_bY : lFln ≠ bY := by decide
@[simp] theorem bY_ne_lFll : bY ≠ lFll := by decide
@[simp] theorem lFll_ne_bY : lFll ≠ bY := by decide
@[simp] theorem bY_ne_lFls : bY ≠ lFls := by decide
@[simp] theorem lFls_ne_bY : lFls ≠ bY := by decide
@[simp] theorem bY_ne_lKb : bY ≠ lKb := by decide
@[simp] theorem lKb_ne_bY : lKb ≠ bY := by decide
@[simp] theorem bR_ne_lFl : bR ≠ lFl := by decide
@[simp] theorem lFl_ne_bR : lFl ≠ bR := by decide
@[simp] theorem bR_ne_lDh : bR ≠ lDh := by decide
@[simp] theorem lDh_ne_bR : lDh ≠ bR := by decide
@[simp] theorem bR_ne_lDt : bR ≠ lDt := by decide
@[simp] theorem lDt_ne_bR : lDt ≠ bR := by decide
@[simp] theorem bR_ne_lDg : bR ≠ lDg := by decide
@[simp] theorem lDg_ne_bR : lDg ≠ bR := by decide
@[simp] theorem bR_ne_lDi : bR ≠ lDi := by decide
@[simp] theorem lDi_ne_bR : lDi ≠ bR := by decide
@[simp] theorem bR_ne_lRp : bR ≠ lRp := by decide
@[simp] theorem lRp_ne_bR : lRp ≠ bR := by decide
@[simp] theorem bR_ne_lRn : bR ≠ lRn := by decide
@[simp] theorem lRn_ne_bR : lRn ≠ bR := by decide
@[simp] theorem bR_ne_lFle : bR ≠ lFle := by decide
@[simp] theorem lFle_ne_bR : lFle ≠ bR := by decide
@[simp] theorem bR_ne_lDir : bR ≠ lDir := by decide
@[simp] theorem lDir_ne_bR : lDir ≠ bR := by decide
@[simp] theorem bR_ne_lFln : bR ≠ lFln := by decide
@[simp] theorem lFln_ne_bR : lFln ≠ bR := by decide
@[simp] theorem bR_ne_lFll : bR ≠ lFll := by decide
@[simp] theorem lFll_ne_bR : lFll ≠ bR := by decide
@[simp] theorem bR_ne_lFls : bR ≠ lFls := by decide
@[simp] theorem lFls_ne_bR : lFls ≠ bR := by decide
@[simp] theorem bR_ne_lKb : bR ≠ lKb := by decide
@[simp] theorem lKb_ne_bR : lKb ≠ bR := by decide
@[simp] theorem bI_ne_lFl : bI ≠ lFl := by decide
@[simp] theorem lFl_ne_bI : lFl ≠ bI := by decide
@[simp] theorem bI_ne_lDh : bI ≠ lDh := by decide
@[simp] theorem lDh_ne_bI : lDh ≠ bI := by decide
@[simp] theorem bI_ne_lDt : bI ≠ lDt := by decide
@[simp] theorem lDt_ne_bI : lDt ≠ bI := by decide
@[simp] theorem bI_ne_lDg : bI ≠ lDg := by decide
@[simp] theorem lDg_ne_bI : lDg ≠ bI := by decide
@[simp] theorem bI_ne_lDi : bI ≠ lDi := by decide
@[simp] theorem lDi_ne_bI : lDi ≠ bI := by decide
@[simp] theorem bI_ne_lRp : bI ≠ lRp := by decide
@[simp] theorem lRp_ne_bI : lRp ≠ bI := by decide
@[simp] theorem bI_ne_lRn : bI ≠ lRn := by decide
@[simp] theorem lRn_ne_bI : lRn ≠ bI := by decide
@[simp] theorem bI_ne_lFle : bI ≠ lFle := by decide
@[simp] theorem lFle_ne_bI : lFle ≠ bI := by decide
@[simp] theorem bI_ne_lDir : bI ≠ lDir := by decide
@[simp] theorem lDir_ne_bI : lDir ≠ bI := by decide
@[simp] theorem bI_ne_lFln : bI ≠ lFln := by decide
@[simp] theorem lFln_ne_bI : lFln ≠ bI := by decide
@[simp] theorem bI_ne_lFll : bI ≠ lFll := by decide
@[simp] theorem lFll_ne_bI : lFll ≠ bI := by decide
@[simp] theorem bI_ne_lFls : bI ≠ lFls := by decide
@[simp] theorem lFls_ne_bI : lFls ≠ bI := by decide
@[simp] theorem bI_ne_lKb : bI ≠ lKb := by decide
@[simp] theorem lKb_ne_bI : lKb ≠ bI := by decide

def bcParams : List MlS := [bA, bB]
def bcLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, bPa, bLa, bQa, bQb, bX, bY, bR, bI]

/-- The verdict update: unchanged unless still `1` (equal so far), then the limbs decide. -/
def updE : ExpHOL 64 :=
  .op .add [vv bR, .panop .mul [.cmp .equal (vv bR) (.const 1),
    .op .sub [.cmp .lower (vv bY) (vv bX), .cmp .lower (vv bX) (vv bY)]]]

def cmpLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv bI) (vv bLa))
    (.seq (.assign .local bQa (.op .sub [vv bQa, .const 8]))
    (.seq (.assign .local bQb (.op .sub [vv bQb, .const 8]))
    (.seq (.assign .local bX (.load .one (vv bQa)))
    (.seq (.assign .local bY (.load .one (vv bQb)))
    (.seq (.assign .local bR updE)
    (.assign .local bI (.op .add [vv bI, .const 1])))))))

def bcCore : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv bA)) (.seq eViewP
  (.seq (.assign .local bPa (vv lRp)) (.seq (.assign .local bLa (.op .sub [vv lRn, .const 1]))
  (.seq (.assign .local lDh (vv bB)) (.seq eViewP
  (.ite (.cmp .lower (vv bLa) (.op .sub [vv lRn, .const 1])) (.return (.const 0))
  (.ite (.cmp .lower (.op .sub [vv lRn, .const 1]) (vv bLa)) (.return (.const 2))
  (.seq (.assign .local bQa (.op .add [vv bPa, .op .add [.panop .mul [vv bLa, .const 8], .const 8]]))
  (.seq (.assign .local bQb (.op .add [vv lRp, .op .add [.panop .mul [vv bLa, .const 8], .const 8]]))
  (.seq (.assign .local bR (.const 1)) (.seq (.assign .local bI (.const 0))
  (.seq cmpLoop (.return (vv bR)))))))))))))))

def bcBody : ProgHOL 64 := prologue bcLocals bcCore

/-! ## The arithmetic of one step -/

theorem div_lt_succ {a b j : Nat} (h : a / B ^ (j + 1) < b / B ^ (j + 1)) : a / B ^ j < b / B ^ j := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at h
  exact lt_of_div_lt h

theorem word_lt_iff (x y : Nat) (hx : x < B) (hy : y < B) :
    BitVec.ofNat 64 x < BitVec.ofNat 64 y ↔ x < y := by
  rw [BitVec.lt_def]; simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem upd_eq (r x y : Nat) (hr : r = 0 ∨ r = 1 ∨ r = 2) (hx : x < B) (hy : y < B) :
    BitVec.ofNat 64 r + (if BitVec.ofNat 64 r = 1 then (1 : BitVec 64) else 0) *
      ((if BitVec.ofNat 64 y < BitVec.ofNat 64 x then (1 : BitVec 64) else 0) -
        (if BitVec.ofNat 64 x < BitVec.ofNat 64 y then (1 : BitVec 64) else 0)) =
      BitVec.ofNat 64 (if r = 1 then (if x < y then 0 else if x = y then 1 else 2) else r) := by
  simp only [word_lt_iff y x hy hx, word_lt_iff x y hx hy]
  rcases hr with rfl | rfl | rfl
  · simp
  · by_cases h1 : x < y
    · have : ¬ y < x := by omega
      simp [h1, this]
    · by_cases h2 : x = y
      · subst h2; simp
      · have : y < x := by omega
        simp [h1, h2, this]
  · simp

theorem cmpN_step {a b j : Nat} :
    cmpN (a / B ^ j) (b / B ^ j) =
      (if cmpN (a / B ^ (j + 1)) (b / B ^ (j + 1)) = 1 then
        (if a / B ^ j % B < b / B ^ j % B then 0 else if a / B ^ j % B = b / B ^ j % B then 1 else 2)
      else cmpN (a / B ^ (j + 1)) (b / B ^ (j + 1))) := by
  unfold cmpN
  by_cases h1 : a / B ^ (j + 1) < b / B ^ (j + 1)
  · simp [h1, div_lt_succ h1]
  by_cases h2 : a / B ^ (j + 1) = b / B ^ (j + 1)
  · obtain ⟨hl, he⟩ := cmp_step h2
    simp only [h1, h2, ite_false, ite_true]
    by_cases h3 : a / B ^ j % B < b / B ^ j % B
    · simp [h3, hl.mpr h3]
    · by_cases h4 : a / B ^ j % B = b / B ^ j % B
      · simp [h3, h4, he.mpr h4]
      · have : ¬ a / B ^ j < b / B ^ j := fun x => h3 (hl.mp x)
        have : ¬ a / B ^ j = b / B ^ j := fun x => h4 (he.mp x)
        simp [*]
  · have h5 : b / B ^ (j + 1) < a / B ^ (j + 1) := by omega
    have h6 := div_lt_succ h5
    have : ¬ a / B ^ j < b / B ^ j := by omega
    have : ¬ a / B ^ j = b / B ^ j := by omega
    simp [*]

section
variable {σ : Type}

/-- The post of a pure word-valued helper: the value, state unchanged. -/
def PostW (C : Ctx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = BitVec.ofNat 64 r ∧ s' = s ∧ SR C s st

theorem postW_locals (C : Ctx) (s : AState) : ∀ (a : Nat) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostW C s a w s' st → PostW C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem specR_envWeak {α : Type} {C : Ctx} {s : AState} {Γa Γb : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hg : ∀ x v, Γb.get x = some v → Γa.get x = some v) (h : SpecR (Inv C s Γb M D) c s m R) :
    SpecR (Inv C s Γa M D) c s m R :=
  fun t ht => h t (inv_envMono ht hg)

theorem bc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bcLocals → (ctxEnv C ++ bcParams.zip vals).get x = none :=
  Knot.params_none C bcLocals bcParams vals (by decide) (by decide)

theorem limbs_len_lt (a : Nat) : (limbs a).length < 2 ^ 61 ∨ True := Or.inr trivial

theorem addr_succ (P : BitVec 64) (j : Nat) :
    P + BitVec.ofNat 64 (8 * (j + 2)) - 8 = P + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [show 8 * (j + 2) = 8 * (j + 1) + 8 by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem addr_init (P : BitVec 64) (l : Nat) :
    P + (BitVec.ofNat 64 l * 8 + 8) = P + BitVec.ofNat 64 (8 * (l + 1)) := by
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  congr 1; omega

/-- The loop's environment after `i` steps. -/
def cmpG (Γ0 : Env) (a b la : Nat) (P P' : BitVec 64) (i : Nat) : Env :=
  (bI, BitVec.ofNat 64 i) :: (bR, BitVec.ofNat 64 (cmpN (a / B ^ (la - i)) (b / B ^ (la - i)))) ::
    (bQb, P' + BitVec.ofNat 64 (8 * (la - i + 1))) :: (bQa, P + BitVec.ofNat 64 (8 * (la - i + 1))) :: Γ0

theorem cmpN_range (x y : Nat) : cmpN x y = 0 ∨ cmpN x y = 1 ∨ cmpN x y = 2 := by
  unfold cmpN
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem sev_updE (Γ : Env) (r x y : BitVec 64) (hr : Γ.get bR = some r) (hx : Γ.get bX = some x)
    (hy : Γ.get bY = some y) :
    sev Γ updE = some (r + (if r = 1 then (1 : BitVec 64) else 0) *
      ((if y < x then (1 : BitVec 64) else 0) - (if x < y then (1 : BitVec 64) else 0))) := by
  simp [updE, sev, hr, hx, hy, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem cmp_loop {α : Type} {C : Ctx} {s : AState} {Γ0 : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (a b la : Nat) (P P' : BitVec 64)
    (hla : (limbs a).length = la) (hlb : (limbs b).length = la) (h61 : la < 2 ^ 61)
    (hD : bQa ∈ D ∧ bQb ∈ D ∧ bX ∈ D ∧ bY ∈ D ∧ bR ∈ D ∧ bI ∈ D)
    (hLa : Γ0.get bLa = some (BitVec.ofNat 64 la)) (hX0 : Γ0.get bX = none) (hY0 : Γ0.get bY = none)
    (hMa : ∀ j (hj : j < (limbs a).length), (P + BitVec.ofNat 64 (8 * (j + 1)), (limbs a)[j]) ∈ M)
    (hMb : ∀ j (hj : j < (limbs b).length), (P' + BitVec.ofNat 64 (8 * (j + 1)), (limbs b)[j]) ∈ M)
    (hr : SpecR (Inv C s (cmpG Γ0 a b la P P' la) M D) rest s m R) :
    SpecR (Inv C s (cmpG Γ0 a b la P P' 0) M D) (.seq cmpLoop rest) s m R := by
  obtain ⟨hqa, hqb, hx, hy, hrr, hiD⟩ := hD
  have hLa' : ∀ i, (cmpG Γ0 a b la P P' i).get bLa = some (BitVec.ofNat 64 la) := by
    intro i; simp [cmpG, Env.get, hLa]
  refine specR_forI (σ := σ) (D := D) _ _ rest la (fun _ => C) (cmpG Γ0 a b la P P')
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 la)
      then 1 else 0, by simp [sev, cmpG, Env.get, hLa], ?_⟩) (fun i hi => ?_) hr
  · have hiB : i < B := by unfold B; omega
    have hlB : la < B := by unfold B; omega
    have e := word_lt_iff i la hiB hlB
    by_cases h : i < la
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h, h]
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 la := fun x => h (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h]
  -- one step at limb `j`
  obtain ⟨j, hj⟩ : ∃ j, la - i = j + 1 := ⟨la - i - 1, by omega⟩
  have hja : j < (limbs a).length := by omega
  have hjb : j < (limbs b).length := by omega
  have e1 : la - i + 1 = j + 2 := by omega
  refine step_seq (step_assignI bQa _ (P + BitVec.ofNat 64 (8 * (j + 1))) hqa
    (by simp +decide [sev, cmpG, Env.get]; rw [e1]; exact addr_succ P j)) ?_
  refine step_seq (step_assignI bQb _ (P' + BitVec.ofNat 64 (8 * (j + 1))) hqb
    (by simp +decide [sev, cmpG, Env.get]; rw [e1]; exact addr_succ P' j)) ?_
  refine step_seq (step_loadI bX (vv bQa) _ (limbs a)[j] hx (by simp +decide [Env.get]) (hMa j hja)) ?_
  refine step_seq (step_loadI bY (vv bQb) _ (limbs b)[j] hy (by simp +decide [Env.get]) (hMb j hjb)) ?_
  have hxa : (limbs a)[j] = BitVec.ofNat 64 (a / B ^ j % B) := limbs_getElem a j hja
  have hyb : (limbs b)[j] = BitVec.ofNat 64 (b / B ^ j % B) := limbs_getElem b j hjb
  have hnew : cmpN (a / B ^ (la - (i + 1))) (b / B ^ (la - (i + 1))) = cmpN (a / B ^ j) (b / B ^ j) := by
    rw [show la - (i + 1) = j by omega]
  refine step_seq (step_assignI bR updE (BitVec.ofNat 64 (cmpN (a / B ^ j) (b / B ^ j))) hrr ?_) ?_
  · rw [sev_updE _ (BitVec.ofNat 64 (cmpN (a / B ^ (la - i)) (b / B ^ (la - i))))
      (BitVec.ofNat 64 (a / B ^ j % B)) (BitVec.ofNat 64 (b / B ^ j % B)) (by simp [cmpG]) (by simp [hxa])
      (by simp [hyb]), hj, upd_eq _ _ _ (cmpN_range _ _) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
      cmpN_step (a := a) (b := b) (j := j)]
  refine step_mono (step_assignI bI _ (BitVec.ofNat 64 (i + 1)) hiD (by simp [sev, cmpG]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun x v hx => ?_))
  simp only [cmpG, Env.get_cons] at hx ⊢
  rw [hnew, show la - (i + 1) + 1 = j + 1 by omega] at hx
  by_cases h1 : x = bI
  · subst h1; simp_all
  by_cases h2 : x = bR
  · subst h2; simp_all
  by_cases h3 : x = bQb
  · subst h3; simp_all
  by_cases h4 : x = bQa
  · subst h4; simp_all
  simp only [h1, h2, h3, h4, ite_false] at hx
  have h5 : x ≠ bY := by intro e; subst e; rw [hY0] at hx; simp at hx
  have h6 : x ≠ bX := by intro e; subst e; rw [hX0] at hx; simp at hx
  simp [h1, h2, h3, h4, h5, h6, cmpG, hx]

theorem add8_eq (l : Nat) : BitVec.ofNat 64 l * 8#64 + 8#64 = BitVec.ofNat 64 (8 * (l + 1)) := by
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  congr 1; omega

theorem div_pow_len (a : Nat) : a / B ^ (limbs a).length = 0 :=
  Nat.div_eq_of_lt ((limbs_length_lt_iff a _).mp (Nat.le_refl _))

theorem cmp_loop' {α : Type} {C : Ctx} {s : AState} {Γ0 : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (a b la : Nat) (P P' : BitVec 64)
    (hla : (limbs a).length = la) (hlb : (limbs b).length = la) (h61 : la < 2 ^ 61)
    (hD : bQa ∈ D ∧ bQb ∈ D ∧ bX ∈ D ∧ bY ∈ D ∧ bR ∈ D ∧ bI ∈ D)
    (hLa : Γ0.get bLa = some (BitVec.ofNat 64 la)) (hX0 : Γ0.get bX = none) (hY0 : Γ0.get bY = none)
    (hMa : ∀ j (hj : j < (limbs a).length), (P + BitVec.ofNat 64 (8 * (j + 1)), (limbs a)[j]) ∈ M)
    (hMb : ∀ j (hj : j < (limbs b).length), (P' + BitVec.ofNat 64 (8 * (j + 1)), (limbs b)[j]) ∈ M)
    (hr : SpecR (Inv C s (cmpG Γ0 a b la P P' la) M D) rest s m R) :
    SpecR (Inv C s ((bI, 0) :: (bR, 1) :: (bQb, P' + BitVec.ofNat 64 (8 * (la + 1))) ::
      (bQa, P + BitVec.ofNat 64 (8 * (la + 1))) :: Γ0) M D) (.seq cmpLoop rest) s m R := by
  have h1 : cmpN (a / B ^ la) (b / B ^ la) = 1 := by
    rw [← hla, div_pow_len, ← hlb.trans hla.symm, div_pow_len]; rfl
  refine specR_envWeak (fun x v hx => ?_) (cmp_loop a b la P P' hla hlb h61 hD hLa hX0 hY0 hMa hMb hr)
  simp only [cmpG, Env.get_cons, Nat.sub_zero, h1] at hx ⊢
  exact hx

theorem bc_spec (C : Ctx) (s : AState) (ha hb : EIdx) (a b : Nat)
    (hva : s.store.view ha = some (.lit (.natVal a))) (hvb : s.store.view hb = some (.lit (.natVal b))) :
    SpecR (σ := σ) (Pre C s (bcParams.zip [Enc.idxW ha, Enc.idxW hb])) bcBody s (pure (cmpN a b)) (PostW C s) := by
  refine specR_prologue (postW_locals C s) (bc_none C _) ?_
  unfold bcCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv bA) (Enc.idxW ha) (by decide) (by simp +decide [Env.get, bcParams, ctxEnv]) ?_
  refine specR_congr (m' := ConRon.Arena.view ha >>= fun _ => pure (cmpN a b))
    (by simp only [bind, StateT.bind]; rw [view_run, hva]; rfl) ?_
  refine ILP.specR_viewIv ha (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv _ hl => ?_)
  rw [hva] at hv; cases hv
  have ea : encEView (.lit (.natVal a)) = 0 :: limbs a := rfl
  rw [ea] at hl ⊢
  simp only [List.length_cons] at hl
  refine specR_assignI bPa (vv lRp) P (by decide) (by simp +decide [Env.get]) ?_
  refine specR_assignI bLa _ (BitVec.ofNat 64 (limbs a).length) (by decide)
    (by simp +decide [sev, Env.get]; exact Ex.ofNat_succ_sub_one _) ?_
  refine specR_assignI lDh (vv bB) (Enc.idxW hb) (by decide) (by simp +decide [Env.get, bcParams, ctxEnv]) ?_
  refine specR_congr (m' := ConRon.Arena.view hb >>= fun _ => pure (cmpN a b))
    (by simp only [bind, StateT.bind]; rw [view_run, hvb]; rfl) ?_
  refine ILP.specR_viewIv hb (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v' P' hv' _ hl' => ?_)
  rw [hvb] at hv'; cases hv'
  have eb : encEView (.lit (.natVal b)) = 0 :: limbs b := rfl
  rw [eb] at hl' ⊢
  simp only [List.length_cons] at hl'
  have hlb : BitVec.ofNat 64 ((limbs b).length + 1) - 1#64 = BitVec.ofNat 64 (limbs b).length :=
    Ex.ofNat_succ_sub_one _
  have hla' : (limbs a).length < B := by unfold B; omega
  have hlb' : (limbs b).length < B := by unfold B; omega
  have w1 := word_lt_iff _ _ hla' hlb'
  have w2 := word_lt_iff _ _ hlb' hla'
  by_cases h1 : (limbs a).length < (limbs b).length
  · refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons, Option.bind_eq_bind]; simp +decide [hlb,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, w1.mpr h1]) (fun _ => ?_) (fun h => absurd h (by decide))
    have : cmpN a b = 0 := by simp [cmpN, lt_of_length_lt h1]
    rw [this]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons, Option.bind_eq_bind]; simp +decide [hlb,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr w1).mpr h1]) (fun h => absurd rfl h) (fun _ => ?_)
  by_cases h2 : (limbs b).length < (limbs a).length
  · refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons, Option.bind_eq_bind]; simp +decide [hlb,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, w2.mpr h2]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hlt := lt_of_length_lt h2
    have : cmpN a b = 2 := by
      have h3 : ¬ a < b := by omega
      have h4 : a ≠ b := by omega
      simp [cmpN, h3, h4]
    rw [this]
    exact specR_returnI _ 2 rfl (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons, Option.bind_eq_bind]; simp +decide [hlb,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr w2).mpr h2]) (fun h => absurd rfl h) (fun _ => ?_)
  have heq : (limbs b).length = (limbs a).length := by omega
  refine specR_assignI bQa _ (P + BitVec.ofNat 64 (8 * ((limbs a).length + 1))) (by decide)
    (by simp [sev, Env.get]; exact add8_eq _) ?_
  refine specR_assignI bQb _ (P' + BitVec.ofNat 64 (8 * ((limbs a).length + 1))) (by decide)
    (by simp [sev, Env.get]; exact add8_eq _) ?_
  refine specR_assignI bR (.const 1) 1 (by decide) rfl ?_
  refine specR_assignI bI (.const 0) 0 (by decide) rfl ?_
  refine cmp_loop' a b (limbs a).length P P' rfl heq (by omega) (by decide) (by simp) (by simp +decide [Env.get, bcParams, ctxEnv])
    (by simp +decide [Env.get, bcParams, ctxEnv])
    (fun j hj => List.mem_append_right _ (wordsAt_get P (0 :: limbs a) (j + 1) (by simp; omega) _))
    (fun j hj => wordsAt_get P' (0 :: limbs b) (j + 1) (by simp; omega) _) ?_
  exact specR_returnI _ (BitVec.ofNat 64 (cmpN a b)) (by simp [cmpG])
    (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Big
