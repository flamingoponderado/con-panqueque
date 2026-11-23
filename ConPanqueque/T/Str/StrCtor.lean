import ConPanqueque.T.Str.Spine
import ConPanqueque.T.SubstLsTop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `strLitToConstructor`: a string literal's constructor form

`String.ofList (List.cons.{0} Char (Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))`: copy the literal's bytes to
the heap, intern the pieces in the twin's order, and build the spine (`strLitSpine`).
-/

namespace ConPanqueque.T.Str

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

def tcH := ofString "tch"
def tcB := ofString "tcb"
def tcL := ofString "tcl"
def tcZ := ofString "tcz"
def tcK := ofString "tck"
def tcZs := ofString "tczs"
def tcCh := ofString "tcch"
def tcE := ofString "tce"
def tcChC := ofString "tcchc"
def tcLn := ofString "tcln"
def tcLnC := ofString "tclnc"
def tcNil := ofString "tcnil"
def tcLc := ofString "tclc"
def tcLcC := ofString "tclcc"
def tcCons := ofString "tccons"
def tcCo := ofString "tcco"
def tcOf := ofString "tcof"
def tcSp := ofString "tcsp"
def tcSl := ofString "tcsl"
def tcSlC := ofString "tcslc"
def tcR := ofString "tcr"
def fTc := ofString "strLitToCtor"

@[simp] theorem tc_tcH_ne_tcB : tcH ≠ tcB := by decide
@[simp] theorem tc_tcH_ne_tcL : tcH ≠ tcL := by decide
@[simp] theorem tc_tcH_ne_tcZ : tcH ≠ tcZ := by decide
@[simp] theorem tc_tcH_ne_tcK : tcH ≠ tcK := by decide
@[simp] theorem tc_tcH_ne_tcZs : tcH ≠ tcZs := by decide
@[simp] theorem tc_tcH_ne_tcCh : tcH ≠ tcCh := by decide
@[simp] theorem tc_tcH_ne_tcE : tcH ≠ tcE := by decide
@[simp] theorem tc_tcH_ne_tcChC : tcH ≠ tcChC := by decide
@[simp] theorem tc_tcH_ne_tcLn : tcH ≠ tcLn := by decide
@[simp] theorem tc_tcH_ne_tcLnC : tcH ≠ tcLnC := by decide
@[simp] theorem tc_tcH_ne_tcNil : tcH ≠ tcNil := by decide
@[simp] theorem tc_tcH_ne_tcLc : tcH ≠ tcLc := by decide
@[simp] theorem tc_tcH_ne_tcLcC : tcH ≠ tcLcC := by decide
@[simp] theorem tc_tcH_ne_tcCons : tcH ≠ tcCons := by decide
@[simp] theorem tc_tcH_ne_tcCo : tcH ≠ tcCo := by decide
@[simp] theorem tc_tcH_ne_tcOf : tcH ≠ tcOf := by decide
@[simp] theorem tc_tcH_ne_tcSp : tcH ≠ tcSp := by decide
@[simp] theorem tc_tcH_ne_tcSl : tcH ≠ tcSl := by decide
@[simp] theorem tc_tcH_ne_tcSlC : tcH ≠ tcSlC := by decide
@[simp] theorem tc_tcH_ne_tcR : tcH ≠ tcR := by decide
@[simp] theorem tc_tcH_ne_lKb : tcH ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcH : lKb ≠ tcH := by decide
@[simp] theorem tc_tcB_ne_tcH : tcB ≠ tcH := by decide
@[simp] theorem tc_tcB_ne_tcL : tcB ≠ tcL := by decide
@[simp] theorem tc_tcB_ne_tcZ : tcB ≠ tcZ := by decide
@[simp] theorem tc_tcB_ne_tcK : tcB ≠ tcK := by decide
@[simp] theorem tc_tcB_ne_tcZs : tcB ≠ tcZs := by decide
@[simp] theorem tc_tcB_ne_tcCh : tcB ≠ tcCh := by decide
@[simp] theorem tc_tcB_ne_tcE : tcB ≠ tcE := by decide
@[simp] theorem tc_tcB_ne_tcChC : tcB ≠ tcChC := by decide
@[simp] theorem tc_tcB_ne_tcLn : tcB ≠ tcLn := by decide
@[simp] theorem tc_tcB_ne_tcLnC : tcB ≠ tcLnC := by decide
@[simp] theorem tc_tcB_ne_tcNil : tcB ≠ tcNil := by decide
@[simp] theorem tc_tcB_ne_tcLc : tcB ≠ tcLc := by decide
@[simp] theorem tc_tcB_ne_tcLcC : tcB ≠ tcLcC := by decide
@[simp] theorem tc_tcB_ne_tcCons : tcB ≠ tcCons := by decide
@[simp] theorem tc_tcB_ne_tcCo : tcB ≠ tcCo := by decide
@[simp] theorem tc_tcB_ne_tcOf : tcB ≠ tcOf := by decide
@[simp] theorem tc_tcB_ne_tcSp : tcB ≠ tcSp := by decide
@[simp] theorem tc_tcB_ne_tcSl : tcB ≠ tcSl := by decide
@[simp] theorem tc_tcB_ne_tcSlC : tcB ≠ tcSlC := by decide
@[simp] theorem tc_tcB_ne_tcR : tcB ≠ tcR := by decide
@[simp] theorem tc_tcB_ne_lKb : tcB ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcB : lKb ≠ tcB := by decide
@[simp] theorem tc_tcL_ne_tcH : tcL ≠ tcH := by decide
@[simp] theorem tc_tcL_ne_tcB : tcL ≠ tcB := by decide
@[simp] theorem tc_tcL_ne_tcZ : tcL ≠ tcZ := by decide
@[simp] theorem tc_tcL_ne_tcK : tcL ≠ tcK := by decide
@[simp] theorem tc_tcL_ne_tcZs : tcL ≠ tcZs := by decide
@[simp] theorem tc_tcL_ne_tcCh : tcL ≠ tcCh := by decide
@[simp] theorem tc_tcL_ne_tcE : tcL ≠ tcE := by decide
@[simp] theorem tc_tcL_ne_tcChC : tcL ≠ tcChC := by decide
@[simp] theorem tc_tcL_ne_tcLn : tcL ≠ tcLn := by decide
@[simp] theorem tc_tcL_ne_tcLnC : tcL ≠ tcLnC := by decide
@[simp] theorem tc_tcL_ne_tcNil : tcL ≠ tcNil := by decide
@[simp] theorem tc_tcL_ne_tcLc : tcL ≠ tcLc := by decide
@[simp] theorem tc_tcL_ne_tcLcC : tcL ≠ tcLcC := by decide
@[simp] theorem tc_tcL_ne_tcCons : tcL ≠ tcCons := by decide
@[simp] theorem tc_tcL_ne_tcCo : tcL ≠ tcCo := by decide
@[simp] theorem tc_tcL_ne_tcOf : tcL ≠ tcOf := by decide
@[simp] theorem tc_tcL_ne_tcSp : tcL ≠ tcSp := by decide
@[simp] theorem tc_tcL_ne_tcSl : tcL ≠ tcSl := by decide
@[simp] theorem tc_tcL_ne_tcSlC : tcL ≠ tcSlC := by decide
@[simp] theorem tc_tcL_ne_tcR : tcL ≠ tcR := by decide
@[simp] theorem tc_tcL_ne_lKb : tcL ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcL : lKb ≠ tcL := by decide
@[simp] theorem tc_tcZ_ne_tcH : tcZ ≠ tcH := by decide
@[simp] theorem tc_tcZ_ne_tcB : tcZ ≠ tcB := by decide
@[simp] theorem tc_tcZ_ne_tcL : tcZ ≠ tcL := by decide
@[simp] theorem tc_tcZ_ne_tcK : tcZ ≠ tcK := by decide
@[simp] theorem tc_tcZ_ne_tcZs : tcZ ≠ tcZs := by decide
@[simp] theorem tc_tcZ_ne_tcCh : tcZ ≠ tcCh := by decide
@[simp] theorem tc_tcZ_ne_tcE : tcZ ≠ tcE := by decide
@[simp] theorem tc_tcZ_ne_tcChC : tcZ ≠ tcChC := by decide
@[simp] theorem tc_tcZ_ne_tcLn : tcZ ≠ tcLn := by decide
@[simp] theorem tc_tcZ_ne_tcLnC : tcZ ≠ tcLnC := by decide
@[simp] theorem tc_tcZ_ne_tcNil : tcZ ≠ tcNil := by decide
@[simp] theorem tc_tcZ_ne_tcLc : tcZ ≠ tcLc := by decide
@[simp] theorem tc_tcZ_ne_tcLcC : tcZ ≠ tcLcC := by decide
@[simp] theorem tc_tcZ_ne_tcCons : tcZ ≠ tcCons := by decide
@[simp] theorem tc_tcZ_ne_tcCo : tcZ ≠ tcCo := by decide
@[simp] theorem tc_tcZ_ne_tcOf : tcZ ≠ tcOf := by decide
@[simp] theorem tc_tcZ_ne_tcSp : tcZ ≠ tcSp := by decide
@[simp] theorem tc_tcZ_ne_tcSl : tcZ ≠ tcSl := by decide
@[simp] theorem tc_tcZ_ne_tcSlC : tcZ ≠ tcSlC := by decide
@[simp] theorem tc_tcZ_ne_tcR : tcZ ≠ tcR := by decide
@[simp] theorem tc_tcZ_ne_lKb : tcZ ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcZ : lKb ≠ tcZ := by decide
@[simp] theorem tc_tcK_ne_tcH : tcK ≠ tcH := by decide
@[simp] theorem tc_tcK_ne_tcB : tcK ≠ tcB := by decide
@[simp] theorem tc_tcK_ne_tcL : tcK ≠ tcL := by decide
@[simp] theorem tc_tcK_ne_tcZ : tcK ≠ tcZ := by decide
@[simp] theorem tc_tcK_ne_tcZs : tcK ≠ tcZs := by decide
@[simp] theorem tc_tcK_ne_tcCh : tcK ≠ tcCh := by decide
@[simp] theorem tc_tcK_ne_tcE : tcK ≠ tcE := by decide
@[simp] theorem tc_tcK_ne_tcChC : tcK ≠ tcChC := by decide
@[simp] theorem tc_tcK_ne_tcLn : tcK ≠ tcLn := by decide
@[simp] theorem tc_tcK_ne_tcLnC : tcK ≠ tcLnC := by decide
@[simp] theorem tc_tcK_ne_tcNil : tcK ≠ tcNil := by decide
@[simp] theorem tc_tcK_ne_tcLc : tcK ≠ tcLc := by decide
@[simp] theorem tc_tcK_ne_tcLcC : tcK ≠ tcLcC := by decide
@[simp] theorem tc_tcK_ne_tcCons : tcK ≠ tcCons := by decide
@[simp] theorem tc_tcK_ne_tcCo : tcK ≠ tcCo := by decide
@[simp] theorem tc_tcK_ne_tcOf : tcK ≠ tcOf := by decide
@[simp] theorem tc_tcK_ne_tcSp : tcK ≠ tcSp := by decide
@[simp] theorem tc_tcK_ne_tcSl : tcK ≠ tcSl := by decide
@[simp] theorem tc_tcK_ne_tcSlC : tcK ≠ tcSlC := by decide
@[simp] theorem tc_tcK_ne_tcR : tcK ≠ tcR := by decide
@[simp] theorem tc_tcK_ne_lKb : tcK ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcK : lKb ≠ tcK := by decide
@[simp] theorem tc_tcZs_ne_tcH : tcZs ≠ tcH := by decide
@[simp] theorem tc_tcZs_ne_tcB : tcZs ≠ tcB := by decide
@[simp] theorem tc_tcZs_ne_tcL : tcZs ≠ tcL := by decide
@[simp] theorem tc_tcZs_ne_tcZ : tcZs ≠ tcZ := by decide
@[simp] theorem tc_tcZs_ne_tcK : tcZs ≠ tcK := by decide
@[simp] theorem tc_tcZs_ne_tcCh : tcZs ≠ tcCh := by decide
@[simp] theorem tc_tcZs_ne_tcE : tcZs ≠ tcE := by decide
@[simp] theorem tc_tcZs_ne_tcChC : tcZs ≠ tcChC := by decide
@[simp] theorem tc_tcZs_ne_tcLn : tcZs ≠ tcLn := by decide
@[simp] theorem tc_tcZs_ne_tcLnC : tcZs ≠ tcLnC := by decide
@[simp] theorem tc_tcZs_ne_tcNil : tcZs ≠ tcNil := by decide
@[simp] theorem tc_tcZs_ne_tcLc : tcZs ≠ tcLc := by decide
@[simp] theorem tc_tcZs_ne_tcLcC : tcZs ≠ tcLcC := by decide
@[simp] theorem tc_tcZs_ne_tcCons : tcZs ≠ tcCons := by decide
@[simp] theorem tc_tcZs_ne_tcCo : tcZs ≠ tcCo := by decide
@[simp] theorem tc_tcZs_ne_tcOf : tcZs ≠ tcOf := by decide
@[simp] theorem tc_tcZs_ne_tcSp : tcZs ≠ tcSp := by decide
@[simp] theorem tc_tcZs_ne_tcSl : tcZs ≠ tcSl := by decide
@[simp] theorem tc_tcZs_ne_tcSlC : tcZs ≠ tcSlC := by decide
@[simp] theorem tc_tcZs_ne_tcR : tcZs ≠ tcR := by decide
@[simp] theorem tc_tcZs_ne_lKb : tcZs ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcZs : lKb ≠ tcZs := by decide
@[simp] theorem tc_tcCh_ne_tcH : tcCh ≠ tcH := by decide
@[simp] theorem tc_tcCh_ne_tcB : tcCh ≠ tcB := by decide
@[simp] theorem tc_tcCh_ne_tcL : tcCh ≠ tcL := by decide
@[simp] theorem tc_tcCh_ne_tcZ : tcCh ≠ tcZ := by decide
@[simp] theorem tc_tcCh_ne_tcK : tcCh ≠ tcK := by decide
@[simp] theorem tc_tcCh_ne_tcZs : tcCh ≠ tcZs := by decide
@[simp] theorem tc_tcCh_ne_tcE : tcCh ≠ tcE := by decide
@[simp] theorem tc_tcCh_ne_tcChC : tcCh ≠ tcChC := by decide
@[simp] theorem tc_tcCh_ne_tcLn : tcCh ≠ tcLn := by decide
@[simp] theorem tc_tcCh_ne_tcLnC : tcCh ≠ tcLnC := by decide
@[simp] theorem tc_tcCh_ne_tcNil : tcCh ≠ tcNil := by decide
@[simp] theorem tc_tcCh_ne_tcLc : tcCh ≠ tcLc := by decide
@[simp] theorem tc_tcCh_ne_tcLcC : tcCh ≠ tcLcC := by decide
@[simp] theorem tc_tcCh_ne_tcCons : tcCh ≠ tcCons := by decide
@[simp] theorem tc_tcCh_ne_tcCo : tcCh ≠ tcCo := by decide
@[simp] theorem tc_tcCh_ne_tcOf : tcCh ≠ tcOf := by decide
@[simp] theorem tc_tcCh_ne_tcSp : tcCh ≠ tcSp := by decide
@[simp] theorem tc_tcCh_ne_tcSl : tcCh ≠ tcSl := by decide
@[simp] theorem tc_tcCh_ne_tcSlC : tcCh ≠ tcSlC := by decide
@[simp] theorem tc_tcCh_ne_tcR : tcCh ≠ tcR := by decide
@[simp] theorem tc_tcCh_ne_lKb : tcCh ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcCh : lKb ≠ tcCh := by decide
@[simp] theorem tc_tcE_ne_tcH : tcE ≠ tcH := by decide
@[simp] theorem tc_tcE_ne_tcB : tcE ≠ tcB := by decide
@[simp] theorem tc_tcE_ne_tcL : tcE ≠ tcL := by decide
@[simp] theorem tc_tcE_ne_tcZ : tcE ≠ tcZ := by decide
@[simp] theorem tc_tcE_ne_tcK : tcE ≠ tcK := by decide
@[simp] theorem tc_tcE_ne_tcZs : tcE ≠ tcZs := by decide
@[simp] theorem tc_tcE_ne_tcCh : tcE ≠ tcCh := by decide
@[simp] theorem tc_tcE_ne_tcChC : tcE ≠ tcChC := by decide
@[simp] theorem tc_tcE_ne_tcLn : tcE ≠ tcLn := by decide
@[simp] theorem tc_tcE_ne_tcLnC : tcE ≠ tcLnC := by decide
@[simp] theorem tc_tcE_ne_tcNil : tcE ≠ tcNil := by decide
@[simp] theorem tc_tcE_ne_tcLc : tcE ≠ tcLc := by decide
@[simp] theorem tc_tcE_ne_tcLcC : tcE ≠ tcLcC := by decide
@[simp] theorem tc_tcE_ne_tcCons : tcE ≠ tcCons := by decide
@[simp] theorem tc_tcE_ne_tcCo : tcE ≠ tcCo := by decide
@[simp] theorem tc_tcE_ne_tcOf : tcE ≠ tcOf := by decide
@[simp] theorem tc_tcE_ne_tcSp : tcE ≠ tcSp := by decide
@[simp] theorem tc_tcE_ne_tcSl : tcE ≠ tcSl := by decide
@[simp] theorem tc_tcE_ne_tcSlC : tcE ≠ tcSlC := by decide
@[simp] theorem tc_tcE_ne_tcR : tcE ≠ tcR := by decide
@[simp] theorem tc_tcE_ne_lKb : tcE ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcE : lKb ≠ tcE := by decide
@[simp] theorem tc_tcChC_ne_tcH : tcChC ≠ tcH := by decide
@[simp] theorem tc_tcChC_ne_tcB : tcChC ≠ tcB := by decide
@[simp] theorem tc_tcChC_ne_tcL : tcChC ≠ tcL := by decide
@[simp] theorem tc_tcChC_ne_tcZ : tcChC ≠ tcZ := by decide
@[simp] theorem tc_tcChC_ne_tcK : tcChC ≠ tcK := by decide
@[simp] theorem tc_tcChC_ne_tcZs : tcChC ≠ tcZs := by decide
@[simp] theorem tc_tcChC_ne_tcCh : tcChC ≠ tcCh := by decide
@[simp] theorem tc_tcChC_ne_tcE : tcChC ≠ tcE := by decide
@[simp] theorem tc_tcChC_ne_tcLn : tcChC ≠ tcLn := by decide
@[simp] theorem tc_tcChC_ne_tcLnC : tcChC ≠ tcLnC := by decide
@[simp] theorem tc_tcChC_ne_tcNil : tcChC ≠ tcNil := by decide
@[simp] theorem tc_tcChC_ne_tcLc : tcChC ≠ tcLc := by decide
@[simp] theorem tc_tcChC_ne_tcLcC : tcChC ≠ tcLcC := by decide
@[simp] theorem tc_tcChC_ne_tcCons : tcChC ≠ tcCons := by decide
@[simp] theorem tc_tcChC_ne_tcCo : tcChC ≠ tcCo := by decide
@[simp] theorem tc_tcChC_ne_tcOf : tcChC ≠ tcOf := by decide
@[simp] theorem tc_tcChC_ne_tcSp : tcChC ≠ tcSp := by decide
@[simp] theorem tc_tcChC_ne_tcSl : tcChC ≠ tcSl := by decide
@[simp] theorem tc_tcChC_ne_tcSlC : tcChC ≠ tcSlC := by decide
@[simp] theorem tc_tcChC_ne_tcR : tcChC ≠ tcR := by decide
@[simp] theorem tc_tcChC_ne_lKb : tcChC ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcChC : lKb ≠ tcChC := by decide
@[simp] theorem tc_tcLn_ne_tcH : tcLn ≠ tcH := by decide
@[simp] theorem tc_tcLn_ne_tcB : tcLn ≠ tcB := by decide
@[simp] theorem tc_tcLn_ne_tcL : tcLn ≠ tcL := by decide
@[simp] theorem tc_tcLn_ne_tcZ : tcLn ≠ tcZ := by decide
@[simp] theorem tc_tcLn_ne_tcK : tcLn ≠ tcK := by decide
@[simp] theorem tc_tcLn_ne_tcZs : tcLn ≠ tcZs := by decide
@[simp] theorem tc_tcLn_ne_tcCh : tcLn ≠ tcCh := by decide
@[simp] theorem tc_tcLn_ne_tcE : tcLn ≠ tcE := by decide
@[simp] theorem tc_tcLn_ne_tcChC : tcLn ≠ tcChC := by decide
@[simp] theorem tc_tcLn_ne_tcLnC : tcLn ≠ tcLnC := by decide
@[simp] theorem tc_tcLn_ne_tcNil : tcLn ≠ tcNil := by decide
@[simp] theorem tc_tcLn_ne_tcLc : tcLn ≠ tcLc := by decide
@[simp] theorem tc_tcLn_ne_tcLcC : tcLn ≠ tcLcC := by decide
@[simp] theorem tc_tcLn_ne_tcCons : tcLn ≠ tcCons := by decide
@[simp] theorem tc_tcLn_ne_tcCo : tcLn ≠ tcCo := by decide
@[simp] theorem tc_tcLn_ne_tcOf : tcLn ≠ tcOf := by decide
@[simp] theorem tc_tcLn_ne_tcSp : tcLn ≠ tcSp := by decide
@[simp] theorem tc_tcLn_ne_tcSl : tcLn ≠ tcSl := by decide
@[simp] theorem tc_tcLn_ne_tcSlC : tcLn ≠ tcSlC := by decide
@[simp] theorem tc_tcLn_ne_tcR : tcLn ≠ tcR := by decide
@[simp] theorem tc_tcLn_ne_lKb : tcLn ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcLn : lKb ≠ tcLn := by decide
@[simp] theorem tc_tcLnC_ne_tcH : tcLnC ≠ tcH := by decide
@[simp] theorem tc_tcLnC_ne_tcB : tcLnC ≠ tcB := by decide
@[simp] theorem tc_tcLnC_ne_tcL : tcLnC ≠ tcL := by decide
@[simp] theorem tc_tcLnC_ne_tcZ : tcLnC ≠ tcZ := by decide
@[simp] theorem tc_tcLnC_ne_tcK : tcLnC ≠ tcK := by decide
@[simp] theorem tc_tcLnC_ne_tcZs : tcLnC ≠ tcZs := by decide
@[simp] theorem tc_tcLnC_ne_tcCh : tcLnC ≠ tcCh := by decide
@[simp] theorem tc_tcLnC_ne_tcE : tcLnC ≠ tcE := by decide
@[simp] theorem tc_tcLnC_ne_tcChC : tcLnC ≠ tcChC := by decide
@[simp] theorem tc_tcLnC_ne_tcLn : tcLnC ≠ tcLn := by decide
@[simp] theorem tc_tcLnC_ne_tcNil : tcLnC ≠ tcNil := by decide
@[simp] theorem tc_tcLnC_ne_tcLc : tcLnC ≠ tcLc := by decide
@[simp] theorem tc_tcLnC_ne_tcLcC : tcLnC ≠ tcLcC := by decide
@[simp] theorem tc_tcLnC_ne_tcCons : tcLnC ≠ tcCons := by decide
@[simp] theorem tc_tcLnC_ne_tcCo : tcLnC ≠ tcCo := by decide
@[simp] theorem tc_tcLnC_ne_tcOf : tcLnC ≠ tcOf := by decide
@[simp] theorem tc_tcLnC_ne_tcSp : tcLnC ≠ tcSp := by decide
@[simp] theorem tc_tcLnC_ne_tcSl : tcLnC ≠ tcSl := by decide
@[simp] theorem tc_tcLnC_ne_tcSlC : tcLnC ≠ tcSlC := by decide
@[simp] theorem tc_tcLnC_ne_tcR : tcLnC ≠ tcR := by decide
@[simp] theorem tc_tcLnC_ne_lKb : tcLnC ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcLnC : lKb ≠ tcLnC := by decide
@[simp] theorem tc_tcNil_ne_tcH : tcNil ≠ tcH := by decide
@[simp] theorem tc_tcNil_ne_tcB : tcNil ≠ tcB := by decide
@[simp] theorem tc_tcNil_ne_tcL : tcNil ≠ tcL := by decide
@[simp] theorem tc_tcNil_ne_tcZ : tcNil ≠ tcZ := by decide
@[simp] theorem tc_tcNil_ne_tcK : tcNil ≠ tcK := by decide
@[simp] theorem tc_tcNil_ne_tcZs : tcNil ≠ tcZs := by decide
@[simp] theorem tc_tcNil_ne_tcCh : tcNil ≠ tcCh := by decide
@[simp] theorem tc_tcNil_ne_tcE : tcNil ≠ tcE := by decide
@[simp] theorem tc_tcNil_ne_tcChC : tcNil ≠ tcChC := by decide
@[simp] theorem tc_tcNil_ne_tcLn : tcNil ≠ tcLn := by decide
@[simp] theorem tc_tcNil_ne_tcLnC : tcNil ≠ tcLnC := by decide
@[simp] theorem tc_tcNil_ne_tcLc : tcNil ≠ tcLc := by decide
@[simp] theorem tc_tcNil_ne_tcLcC : tcNil ≠ tcLcC := by decide
@[simp] theorem tc_tcNil_ne_tcCons : tcNil ≠ tcCons := by decide
@[simp] theorem tc_tcNil_ne_tcCo : tcNil ≠ tcCo := by decide
@[simp] theorem tc_tcNil_ne_tcOf : tcNil ≠ tcOf := by decide
@[simp] theorem tc_tcNil_ne_tcSp : tcNil ≠ tcSp := by decide
@[simp] theorem tc_tcNil_ne_tcSl : tcNil ≠ tcSl := by decide
@[simp] theorem tc_tcNil_ne_tcSlC : tcNil ≠ tcSlC := by decide
@[simp] theorem tc_tcNil_ne_tcR : tcNil ≠ tcR := by decide
@[simp] theorem tc_tcNil_ne_lKb : tcNil ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcNil : lKb ≠ tcNil := by decide
@[simp] theorem tc_tcLc_ne_tcH : tcLc ≠ tcH := by decide
@[simp] theorem tc_tcLc_ne_tcB : tcLc ≠ tcB := by decide
@[simp] theorem tc_tcLc_ne_tcL : tcLc ≠ tcL := by decide
@[simp] theorem tc_tcLc_ne_tcZ : tcLc ≠ tcZ := by decide
@[simp] theorem tc_tcLc_ne_tcK : tcLc ≠ tcK := by decide
@[simp] theorem tc_tcLc_ne_tcZs : tcLc ≠ tcZs := by decide
@[simp] theorem tc_tcLc_ne_tcCh : tcLc ≠ tcCh := by decide
@[simp] theorem tc_tcLc_ne_tcE : tcLc ≠ tcE := by decide
@[simp] theorem tc_tcLc_ne_tcChC : tcLc ≠ tcChC := by decide
@[simp] theorem tc_tcLc_ne_tcLn : tcLc ≠ tcLn := by decide
@[simp] theorem tc_tcLc_ne_tcLnC : tcLc ≠ tcLnC := by decide
@[simp] theorem tc_tcLc_ne_tcNil : tcLc ≠ tcNil := by decide
@[simp] theorem tc_tcLc_ne_tcLcC : tcLc ≠ tcLcC := by decide
@[simp] theorem tc_tcLc_ne_tcCons : tcLc ≠ tcCons := by decide
@[simp] theorem tc_tcLc_ne_tcCo : tcLc ≠ tcCo := by decide
@[simp] theorem tc_tcLc_ne_tcOf : tcLc ≠ tcOf := by decide
@[simp] theorem tc_tcLc_ne_tcSp : tcLc ≠ tcSp := by decide
@[simp] theorem tc_tcLc_ne_tcSl : tcLc ≠ tcSl := by decide
@[simp] theorem tc_tcLc_ne_tcSlC : tcLc ≠ tcSlC := by decide
@[simp] theorem tc_tcLc_ne_tcR : tcLc ≠ tcR := by decide
@[simp] theorem tc_tcLc_ne_lKb : tcLc ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcLc : lKb ≠ tcLc := by decide
@[simp] theorem tc_tcLcC_ne_tcH : tcLcC ≠ tcH := by decide
@[simp] theorem tc_tcLcC_ne_tcB : tcLcC ≠ tcB := by decide
@[simp] theorem tc_tcLcC_ne_tcL : tcLcC ≠ tcL := by decide
@[simp] theorem tc_tcLcC_ne_tcZ : tcLcC ≠ tcZ := by decide
@[simp] theorem tc_tcLcC_ne_tcK : tcLcC ≠ tcK := by decide
@[simp] theorem tc_tcLcC_ne_tcZs : tcLcC ≠ tcZs := by decide
@[simp] theorem tc_tcLcC_ne_tcCh : tcLcC ≠ tcCh := by decide
@[simp] theorem tc_tcLcC_ne_tcE : tcLcC ≠ tcE := by decide
@[simp] theorem tc_tcLcC_ne_tcChC : tcLcC ≠ tcChC := by decide
@[simp] theorem tc_tcLcC_ne_tcLn : tcLcC ≠ tcLn := by decide
@[simp] theorem tc_tcLcC_ne_tcLnC : tcLcC ≠ tcLnC := by decide
@[simp] theorem tc_tcLcC_ne_tcNil : tcLcC ≠ tcNil := by decide
@[simp] theorem tc_tcLcC_ne_tcLc : tcLcC ≠ tcLc := by decide
@[simp] theorem tc_tcLcC_ne_tcCons : tcLcC ≠ tcCons := by decide
@[simp] theorem tc_tcLcC_ne_tcCo : tcLcC ≠ tcCo := by decide
@[simp] theorem tc_tcLcC_ne_tcOf : tcLcC ≠ tcOf := by decide
@[simp] theorem tc_tcLcC_ne_tcSp : tcLcC ≠ tcSp := by decide
@[simp] theorem tc_tcLcC_ne_tcSl : tcLcC ≠ tcSl := by decide
@[simp] theorem tc_tcLcC_ne_tcSlC : tcLcC ≠ tcSlC := by decide
@[simp] theorem tc_tcLcC_ne_tcR : tcLcC ≠ tcR := by decide
@[simp] theorem tc_tcLcC_ne_lKb : tcLcC ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcLcC : lKb ≠ tcLcC := by decide
@[simp] theorem tc_tcCons_ne_tcH : tcCons ≠ tcH := by decide
@[simp] theorem tc_tcCons_ne_tcB : tcCons ≠ tcB := by decide
@[simp] theorem tc_tcCons_ne_tcL : tcCons ≠ tcL := by decide
@[simp] theorem tc_tcCons_ne_tcZ : tcCons ≠ tcZ := by decide
@[simp] theorem tc_tcCons_ne_tcK : tcCons ≠ tcK := by decide
@[simp] theorem tc_tcCons_ne_tcZs : tcCons ≠ tcZs := by decide
@[simp] theorem tc_tcCons_ne_tcCh : tcCons ≠ tcCh := by decide
@[simp] theorem tc_tcCons_ne_tcE : tcCons ≠ tcE := by decide
@[simp] theorem tc_tcCons_ne_tcChC : tcCons ≠ tcChC := by decide
@[simp] theorem tc_tcCons_ne_tcLn : tcCons ≠ tcLn := by decide
@[simp] theorem tc_tcCons_ne_tcLnC : tcCons ≠ tcLnC := by decide
@[simp] theorem tc_tcCons_ne_tcNil : tcCons ≠ tcNil := by decide
@[simp] theorem tc_tcCons_ne_tcLc : tcCons ≠ tcLc := by decide
@[simp] theorem tc_tcCons_ne_tcLcC : tcCons ≠ tcLcC := by decide
@[simp] theorem tc_tcCons_ne_tcCo : tcCons ≠ tcCo := by decide
@[simp] theorem tc_tcCons_ne_tcOf : tcCons ≠ tcOf := by decide
@[simp] theorem tc_tcCons_ne_tcSp : tcCons ≠ tcSp := by decide
@[simp] theorem tc_tcCons_ne_tcSl : tcCons ≠ tcSl := by decide
@[simp] theorem tc_tcCons_ne_tcSlC : tcCons ≠ tcSlC := by decide
@[simp] theorem tc_tcCons_ne_tcR : tcCons ≠ tcR := by decide
@[simp] theorem tc_tcCons_ne_lKb : tcCons ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcCons : lKb ≠ tcCons := by decide
@[simp] theorem tc_tcCo_ne_tcH : tcCo ≠ tcH := by decide
@[simp] theorem tc_tcCo_ne_tcB : tcCo ≠ tcB := by decide
@[simp] theorem tc_tcCo_ne_tcL : tcCo ≠ tcL := by decide
@[simp] theorem tc_tcCo_ne_tcZ : tcCo ≠ tcZ := by decide
@[simp] theorem tc_tcCo_ne_tcK : tcCo ≠ tcK := by decide
@[simp] theorem tc_tcCo_ne_tcZs : tcCo ≠ tcZs := by decide
@[simp] theorem tc_tcCo_ne_tcCh : tcCo ≠ tcCh := by decide
@[simp] theorem tc_tcCo_ne_tcE : tcCo ≠ tcE := by decide
@[simp] theorem tc_tcCo_ne_tcChC : tcCo ≠ tcChC := by decide
@[simp] theorem tc_tcCo_ne_tcLn : tcCo ≠ tcLn := by decide
@[simp] theorem tc_tcCo_ne_tcLnC : tcCo ≠ tcLnC := by decide
@[simp] theorem tc_tcCo_ne_tcNil : tcCo ≠ tcNil := by decide
@[simp] theorem tc_tcCo_ne_tcLc : tcCo ≠ tcLc := by decide
@[simp] theorem tc_tcCo_ne_tcLcC : tcCo ≠ tcLcC := by decide
@[simp] theorem tc_tcCo_ne_tcCons : tcCo ≠ tcCons := by decide
@[simp] theorem tc_tcCo_ne_tcOf : tcCo ≠ tcOf := by decide
@[simp] theorem tc_tcCo_ne_tcSp : tcCo ≠ tcSp := by decide
@[simp] theorem tc_tcCo_ne_tcSl : tcCo ≠ tcSl := by decide
@[simp] theorem tc_tcCo_ne_tcSlC : tcCo ≠ tcSlC := by decide
@[simp] theorem tc_tcCo_ne_tcR : tcCo ≠ tcR := by decide
@[simp] theorem tc_tcCo_ne_lKb : tcCo ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcCo : lKb ≠ tcCo := by decide
@[simp] theorem tc_tcOf_ne_tcH : tcOf ≠ tcH := by decide
@[simp] theorem tc_tcOf_ne_tcB : tcOf ≠ tcB := by decide
@[simp] theorem tc_tcOf_ne_tcL : tcOf ≠ tcL := by decide
@[simp] theorem tc_tcOf_ne_tcZ : tcOf ≠ tcZ := by decide
@[simp] theorem tc_tcOf_ne_tcK : tcOf ≠ tcK := by decide
@[simp] theorem tc_tcOf_ne_tcZs : tcOf ≠ tcZs := by decide
@[simp] theorem tc_tcOf_ne_tcCh : tcOf ≠ tcCh := by decide
@[simp] theorem tc_tcOf_ne_tcE : tcOf ≠ tcE := by decide
@[simp] theorem tc_tcOf_ne_tcChC : tcOf ≠ tcChC := by decide
@[simp] theorem tc_tcOf_ne_tcLn : tcOf ≠ tcLn := by decide
@[simp] theorem tc_tcOf_ne_tcLnC : tcOf ≠ tcLnC := by decide
@[simp] theorem tc_tcOf_ne_tcNil : tcOf ≠ tcNil := by decide
@[simp] theorem tc_tcOf_ne_tcLc : tcOf ≠ tcLc := by decide
@[simp] theorem tc_tcOf_ne_tcLcC : tcOf ≠ tcLcC := by decide
@[simp] theorem tc_tcOf_ne_tcCons : tcOf ≠ tcCons := by decide
@[simp] theorem tc_tcOf_ne_tcCo : tcOf ≠ tcCo := by decide
@[simp] theorem tc_tcOf_ne_tcSp : tcOf ≠ tcSp := by decide
@[simp] theorem tc_tcOf_ne_tcSl : tcOf ≠ tcSl := by decide
@[simp] theorem tc_tcOf_ne_tcSlC : tcOf ≠ tcSlC := by decide
@[simp] theorem tc_tcOf_ne_tcR : tcOf ≠ tcR := by decide
@[simp] theorem tc_tcOf_ne_lKb : tcOf ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcOf : lKb ≠ tcOf := by decide
@[simp] theorem tc_tcSp_ne_tcH : tcSp ≠ tcH := by decide
@[simp] theorem tc_tcSp_ne_tcB : tcSp ≠ tcB := by decide
@[simp] theorem tc_tcSp_ne_tcL : tcSp ≠ tcL := by decide
@[simp] theorem tc_tcSp_ne_tcZ : tcSp ≠ tcZ := by decide
@[simp] theorem tc_tcSp_ne_tcK : tcSp ≠ tcK := by decide
@[simp] theorem tc_tcSp_ne_tcZs : tcSp ≠ tcZs := by decide
@[simp] theorem tc_tcSp_ne_tcCh : tcSp ≠ tcCh := by decide
@[simp] theorem tc_tcSp_ne_tcE : tcSp ≠ tcE := by decide
@[simp] theorem tc_tcSp_ne_tcChC : tcSp ≠ tcChC := by decide
@[simp] theorem tc_tcSp_ne_tcLn : tcSp ≠ tcLn := by decide
@[simp] theorem tc_tcSp_ne_tcLnC : tcSp ≠ tcLnC := by decide
@[simp] theorem tc_tcSp_ne_tcNil : tcSp ≠ tcNil := by decide
@[simp] theorem tc_tcSp_ne_tcLc : tcSp ≠ tcLc := by decide
@[simp] theorem tc_tcSp_ne_tcLcC : tcSp ≠ tcLcC := by decide
@[simp] theorem tc_tcSp_ne_tcCons : tcSp ≠ tcCons := by decide
@[simp] theorem tc_tcSp_ne_tcCo : tcSp ≠ tcCo := by decide
@[simp] theorem tc_tcSp_ne_tcOf : tcSp ≠ tcOf := by decide
@[simp] theorem tc_tcSp_ne_tcSl : tcSp ≠ tcSl := by decide
@[simp] theorem tc_tcSp_ne_tcSlC : tcSp ≠ tcSlC := by decide
@[simp] theorem tc_tcSp_ne_tcR : tcSp ≠ tcR := by decide
@[simp] theorem tc_tcSp_ne_lKb : tcSp ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcSp : lKb ≠ tcSp := by decide
@[simp] theorem tc_tcSl_ne_tcH : tcSl ≠ tcH := by decide
@[simp] theorem tc_tcSl_ne_tcB : tcSl ≠ tcB := by decide
@[simp] theorem tc_tcSl_ne_tcL : tcSl ≠ tcL := by decide
@[simp] theorem tc_tcSl_ne_tcZ : tcSl ≠ tcZ := by decide
@[simp] theorem tc_tcSl_ne_tcK : tcSl ≠ tcK := by decide
@[simp] theorem tc_tcSl_ne_tcZs : tcSl ≠ tcZs := by decide
@[simp] theorem tc_tcSl_ne_tcCh : tcSl ≠ tcCh := by decide
@[simp] theorem tc_tcSl_ne_tcE : tcSl ≠ tcE := by decide
@[simp] theorem tc_tcSl_ne_tcChC : tcSl ≠ tcChC := by decide
@[simp] theorem tc_tcSl_ne_tcLn : tcSl ≠ tcLn := by decide
@[simp] theorem tc_tcSl_ne_tcLnC : tcSl ≠ tcLnC := by decide
@[simp] theorem tc_tcSl_ne_tcNil : tcSl ≠ tcNil := by decide
@[simp] theorem tc_tcSl_ne_tcLc : tcSl ≠ tcLc := by decide
@[simp] theorem tc_tcSl_ne_tcLcC : tcSl ≠ tcLcC := by decide
@[simp] theorem tc_tcSl_ne_tcCons : tcSl ≠ tcCons := by decide
@[simp] theorem tc_tcSl_ne_tcCo : tcSl ≠ tcCo := by decide
@[simp] theorem tc_tcSl_ne_tcOf : tcSl ≠ tcOf := by decide
@[simp] theorem tc_tcSl_ne_tcSp : tcSl ≠ tcSp := by decide
@[simp] theorem tc_tcSl_ne_tcSlC : tcSl ≠ tcSlC := by decide
@[simp] theorem tc_tcSl_ne_tcR : tcSl ≠ tcR := by decide
@[simp] theorem tc_tcSl_ne_lKb : tcSl ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcSl : lKb ≠ tcSl := by decide
@[simp] theorem tc_tcSlC_ne_tcH : tcSlC ≠ tcH := by decide
@[simp] theorem tc_tcSlC_ne_tcB : tcSlC ≠ tcB := by decide
@[simp] theorem tc_tcSlC_ne_tcL : tcSlC ≠ tcL := by decide
@[simp] theorem tc_tcSlC_ne_tcZ : tcSlC ≠ tcZ := by decide
@[simp] theorem tc_tcSlC_ne_tcK : tcSlC ≠ tcK := by decide
@[simp] theorem tc_tcSlC_ne_tcZs : tcSlC ≠ tcZs := by decide
@[simp] theorem tc_tcSlC_ne_tcCh : tcSlC ≠ tcCh := by decide
@[simp] theorem tc_tcSlC_ne_tcE : tcSlC ≠ tcE := by decide
@[simp] theorem tc_tcSlC_ne_tcChC : tcSlC ≠ tcChC := by decide
@[simp] theorem tc_tcSlC_ne_tcLn : tcSlC ≠ tcLn := by decide
@[simp] theorem tc_tcSlC_ne_tcLnC : tcSlC ≠ tcLnC := by decide
@[simp] theorem tc_tcSlC_ne_tcNil : tcSlC ≠ tcNil := by decide
@[simp] theorem tc_tcSlC_ne_tcLc : tcSlC ≠ tcLc := by decide
@[simp] theorem tc_tcSlC_ne_tcLcC : tcSlC ≠ tcLcC := by decide
@[simp] theorem tc_tcSlC_ne_tcCons : tcSlC ≠ tcCons := by decide
@[simp] theorem tc_tcSlC_ne_tcCo : tcSlC ≠ tcCo := by decide
@[simp] theorem tc_tcSlC_ne_tcOf : tcSlC ≠ tcOf := by decide
@[simp] theorem tc_tcSlC_ne_tcSp : tcSlC ≠ tcSp := by decide
@[simp] theorem tc_tcSlC_ne_tcSl : tcSlC ≠ tcSl := by decide
@[simp] theorem tc_tcSlC_ne_tcR : tcSlC ≠ tcR := by decide
@[simp] theorem tc_tcSlC_ne_lKb : tcSlC ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcSlC : lKb ≠ tcSlC := by decide
@[simp] theorem tc_tcR_ne_tcH : tcR ≠ tcH := by decide
@[simp] theorem tc_tcR_ne_tcB : tcR ≠ tcB := by decide
@[simp] theorem tc_tcR_ne_tcL : tcR ≠ tcL := by decide
@[simp] theorem tc_tcR_ne_tcZ : tcR ≠ tcZ := by decide
@[simp] theorem tc_tcR_ne_tcK : tcR ≠ tcK := by decide
@[simp] theorem tc_tcR_ne_tcZs : tcR ≠ tcZs := by decide
@[simp] theorem tc_tcR_ne_tcCh : tcR ≠ tcCh := by decide
@[simp] theorem tc_tcR_ne_tcE : tcR ≠ tcE := by decide
@[simp] theorem tc_tcR_ne_tcChC : tcR ≠ tcChC := by decide
@[simp] theorem tc_tcR_ne_tcLn : tcR ≠ tcLn := by decide
@[simp] theorem tc_tcR_ne_tcLnC : tcR ≠ tcLnC := by decide
@[simp] theorem tc_tcR_ne_tcNil : tcR ≠ tcNil := by decide
@[simp] theorem tc_tcR_ne_tcLc : tcR ≠ tcLc := by decide
@[simp] theorem tc_tcR_ne_tcLcC : tcR ≠ tcLcC := by decide
@[simp] theorem tc_tcR_ne_tcCons : tcR ≠ tcCons := by decide
@[simp] theorem tc_tcR_ne_tcCo : tcR ≠ tcCo := by decide
@[simp] theorem tc_tcR_ne_tcOf : tcR ≠ tcOf := by decide
@[simp] theorem tc_tcR_ne_tcSp : tcR ≠ tcSp := by decide
@[simp] theorem tc_tcR_ne_tcSl : tcR ≠ tcSl := by decide
@[simp] theorem tc_tcR_ne_tcSlC : tcR ≠ tcSlC := by decide
@[simp] theorem tc_tcR_ne_lKb : tcR ≠ lKb := by decide
@[simp] theorem tc_lKb_ne_tcR : lKb ≠ tcR := by decide


def tcLocals : List MlS := [tcB, tcL, tcZ, tcK, tcZs, tcCh, tcE, tcChC, tcLn, tcLnC, tcNil, tcLc, tcLcC, tcCons, tcCo, tcOf, tcSp, tcSl, tcSlC, tcR]

def tcCore (C : Ctx) : ProgHOL 64 :=
  (.seq (.call (some (some (.local, tcB), none)) fLitH [vv tcH])
  (.seq (.assign .local tcL (.load .one (vv tcB)))
  (.seq (.assign .local tcZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (allocP C tcK (.const 8)
  (.seq (.store (vv tcK) (vv tcZ))
  (.seq (.call (some (some (.local, tcZs), none)) fInternLs [vv tcK, .const 1])
  (.seq (.assign .local tcCh (.load .one (.const (ecell C (C.PO + PIN_CHAR)))))
  (.seq (.assign .local tcE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, tcChC), none)) fInternConst [vv tcCh, vv tcE])
  (.seq (.assign .local tcLn (.load .one (.const (ecell C (C.PO + PIN_LIST_NIL)))))
  (.seq (.call (some (some (.local, tcLnC), none)) fInternConst [vv tcLn, vv tcZs])
  (.seq (.call (some (some (.local, tcNil), none)) fInternApp [vv tcLnC, vv tcChC])
  (.seq (.assign .local tcLc (.load .one (.const (ecell C (C.PO + PIN_LIST_CONS)))))
  (.seq (.call (some (some (.local, tcLcC), none)) fInternConst [vv tcLc, vv tcZs])
  (.seq (.call (some (some (.local, tcCons), none)) fInternApp [vv tcLcC, vv tcChC])
  (.seq (.assign .local tcCo (.load .one (.const (ecell C (C.PO + PIN_CHAR_OF_NAT)))))
  (.seq (.assign .local tcE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, tcOf), none)) fInternConst [vv tcCo, vv tcE])
  (.seq (.call (some (some (.local, tcSp), none)) fSl [vv tcCons, vv tcOf, vv tcNil, vv tcB, .const 0, vv tcL])
  (.seq (.assign .local tcSl (.load .one (.const (ecell C (C.PO + PIN_STRING_OF_LIST)))))
  (.seq (.assign .local tcE (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, tcSlC), none)) fInternConst [vv tcSl, vv tcE])
  (.seq (.call (some (some (.local, tcR), none)) fInternApp [vv tcSlC, vv tcSp])
  (.return (vv tcR)))))))))))))))))))))))))

def tcBody (C : Ctx) : ProgHOL 64 := prologue tcLocals (tcCore C)

section
variable {σ : Type}

theorem tc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tcLocals → (ctxEnv C ++ [tcH].zip vals).get x = none :=
  Knot.params_none C tcLocals [tcH] vals (by decide) (by decide)

theorem strW_bytes (str : String) :
    Enc.strW str = (str.toByteArray.data.toList.map UInt8.toNat).map (BitVec.ofNat 64) := by
  simp [Enc.strW, List.map_map]

theorem bytes_chars (str : String) :
    str.toByteArray.data.toList.map UInt8.toNat = (str.toList.flatMap String.utf8EncodeChar).map UInt8.toNat := by
  conv => lhs; rw [← String.ofList_toList (s := str), String.toByteArray_ofList]
  simp only [List.utf8Encode, List.data_toByteArray]

theorem slCodes_H {C : Ctx} (hc : SlCodes C) (H : List (BitVec 64)) : SlCodes (ctxH C H) :=
  ⟨hc.sl, hc.lw, hc.lb, hc.ia⟩

/-- The code `strLitToCtor` calls. -/
structure TcCodes (C : Ctx) : Prop where
  sl : SlCodes C
  lit : C.code.lookup fLitH = some ([cH].map (fun p => (p, ShapeHOL.one)), litBody C, .one)
  ls : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)

/-- Call a `PostG` helper (a fresh block holding `ws`, state unchanged) whose twin is `pure ()`. -/
theorem specR_callPG {β : Type} {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (ws : List (BitVec 64)) (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (σ := σ) (Pre C s (ps.zip vs)) Bd s (pure () : AM Unit) (PostG C s ws))
    (hk : ∀ H' o, C.H <+: H' → BlkAt H' o ws →
      SpecR (Inv (ctxH C H') s ((x, cellA C o) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (.seq (.call (some (some (.local, x), none)) f es) rest) s m R := by
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => m) rfl ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes (PostG C s ws)
    (fun _ w s' H2 => s' = s ∧ ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 ws)
    (fun _ w s' st ⟨H2, o2, hp, hw, hb, hs, hsr⟩ => ⟨H2, hp, ⟨hs, o2, hw, hb⟩, hs ▸ hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec)
    (fun _ w s' H2 hp2 ⟨hs, o2, hw, hb2⟩ => ?_)
  subst hs hw
  exact hk H2 o2 hp2 hb2

theorem tc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TcCodes C)
    (s : AState) (h : EIdx) (str : String) (hv : s.store.view h = some (.lit (.strVal str))) :
    SpecR (σ := σ) (Pre C s [(tcH, Enc.idxW h)]) (tcBody C) s (strLitToConstructor str) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (tc_none C [Enc.idxW h]) ?_
  unfold tcCore
  simp only [strLitToConstructor, constE, emptyLevels, zeroLevel, pinChar, pinListNil, pinListCons, pinCharOfNat,
    pinStringOfList, bind_assoc]
  refine specR_callPG tcB fLitH [cH] [vv tcH] (litBody C) [Enc.idxW h] (Enc.strW str) (by decide) rfl (by decide)
    hc.lit ⟨by simp +decide [Env.get, ctxEnv], trivial⟩ (litg_spec C hok s h _ 1 (Enc.strW str) hv rfl)
    (fun H1 o hp1 hb => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) tcL (vv tcB) o _ hb.1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hsl := blk_small0 (C := ctxH C H1) (ctxOK_H hok _) ht0.sr hb
  refine specR_pinXI (C := ctxH C H1) (ctxOK_H hok _) pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H1) (ctxOK_H hok _) hp) (pin_zeroLevel_cell (ctxOK_H hok H1)) tcZ (by decide) ?_
  refine specR_allocI (C := ctxH C H1) tcK (.const 8) 1 (by norm_num) (by decide) (fun _ => by simp [sev])
    (fun H3 ws3 hpre hwl hcap => ?_)
  have hpl := hpre.length_le
  have hj : H3.length < (ctxH (ctxH C H1) (H3 ++ ws3)).H.length := by show _ < (H3 ++ ws3).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv tcK) (vv tcZ) _ hj (Enc.idxW C.pins.zeroLevel) (by simp; rfl)
    (by simp; rfl) ?_
  let H4 := (H3 ++ ws3).set H3.length (Enc.idxW C.pins.zeroLevel)
  have hp34 : H3 <+: H4 := prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
  have hp13 : H1 <+: H3 := hpre
  refine specR_callNIA (C := ctxH C H4) tcZs fInternLs [pKey, lEc] [vv tcK, .const 1] internLsBody
    [cellA C H3.length, BitVec.ofNat 64 1] (by decide) rfl (by decide) hc.ls
    ⟨by simp; rfl, rfl, trivial⟩
    (fun a w s' st => internLsNode [C.pins.zeroLevel] s = .ok (a, s') ∧ PostLs (ctxH (ctxH C H4) H3) a w s' st)
    (fun a w s' H' => H' = H3 ∧ internLsNode [C.pins.zeroLevel] s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H3, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact internLs_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s [C.pins.zeroLevel] H3.length H3 hp34
        (le_refl _) (by show H3.length + 1 ≤ H4.length; simp [H4]; omega) (by norm_num)
        (fun j hj => by
          have : j = 0 := by simpa using hj
          subst this
          show ((H3 ++ ws3).set H3.length _)[H3.length + 0]? = _
          rw [Nat.add_zero, List.getElem?_set_self (by simp; omega)]; rfl)
        _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
    (fun zs w s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst H'; subst hw
  refine specR_pinAtI (C := ctxH C H3) (ctxOK_H hok _) PIN_CHAR (by decide) tcCh (by decide) ?_
  refine specR_pinXI (C := ctxH C H3) (ctxOK_H hok _) pinEmptyLevels 0 C.pins.emptyLevels _
    (fun s hp => pinEmptyLevels_run (C := ctxH C H3) (ctxOK_H hok _) hp) (pin_emptyLevels_cell (ctxOK_H hok H3)) tcE (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H3) tcChC fInternConst [lEn, lEus] [vv tcCh, vv tcE] constBody
    [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩ (by exact const_body_spec ra (ctxH C H3) (ctxOK_H hok _) s2 _ _) (fun chC s3 => ?_)
  refine specR_pinAtI (C := ctxH C H3) (ctxOK_H hok _) PIN_LIST_NIL (by decide) tcLn (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H3) tcLnC fInternConst [lEn, lEus] [vv tcLn, vv tcZs] constBody
    [_, Enc.idxW zs] (by decide) rfl (by decide) hc.ic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩ (by exact const_body_spec ra (ctxH C H3) (ctxOK_H hok _) s3 _ _) (fun lnC s4 => ?_)
  refine specR_internAppI (C := ctxH C H3) ra (ctxOK_H hok _) hc.sl.ia tcNil (vv tcLnC) (vv tcChC) lnC chC
    (by decide) (by simp) (by simp) (fun nilE s5 => ?_)
  refine specR_pinAtI (C := ctxH C H3) (ctxOK_H hok _) PIN_LIST_CONS (by decide) tcLc (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H3) tcLcC fInternConst [lEn, lEus] [vv tcLc, vv tcZs] constBody
    [_, Enc.idxW zs] (by decide) rfl (by decide) hc.ic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩ (by exact const_body_spec ra (ctxH C H3) (ctxOK_H hok _) s5 _ _) (fun lcC s6 => ?_)
  refine specR_internAppI (C := ctxH C H3) ra (ctxOK_H hok _) hc.sl.ia tcCons (vv tcLcC) (vv tcChC) lcC chC
    (by decide) (by simp) (by simp) (fun consE s7 => ?_)
  refine specR_pinAtI (C := ctxH C H3) (ctxOK_H hok _) PIN_CHAR_OF_NAT (by decide) tcCo (by decide) ?_
  refine specR_pinXI (C := ctxH C H3) (ctxOK_H hok _) pinEmptyLevels 0 C.pins.emptyLevels _
    (fun s hp => pinEmptyLevels_run (C := ctxH C H3) (ctxOK_H hok _) hp) (pin_emptyLevels_cell (ctxOK_H hok H3)) tcE (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H3) tcOf fInternConst [lEn, lEus] [vv tcCo, vv tcE] constBody
    [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩ (by exact const_body_spec ra (ctxH C H3) (ctxOK_H hok _) s7 _ _) (fun ofE s8 => ?_)
  have hbs : BlkAt H3 o ((str.toByteArray.data.toList.map UInt8.toNat).map (BitVec.ofNat 64)) := by
    rw [← strW_bytes]; exact blkAt_mono hb hp13
  have hlen : (str.toByteArray.data.toList.map UInt8.toNat).length < 2 ^ 58 := by
    have := hsl; rw [strW_bytes] at this; simpa using this
  refine specR_callKH (C := ctxH C H3) tcSp fSl slParams [vv tcCons, vv tcOf, vv tcNil, vv tcB, .const 0, vv tcL]
    slBody [Enc.idxW consE, Enc.idxW ofE, Enc.idxW nilE, cellA C o, BitVec.ofNat 64 0,
      BitVec.ofNat 64 (str.toByteArray.data.toList.map UInt8.toNat).length] (by decide) rfl (by decide) hc.sl.sl
    ⟨by simp, by simp, by simp, by simp, rfl, by simp [strW_bytes], trivial⟩
    (sl_spec ra (ctxH C H3) (ctxOK_H hok _) (slCodes_H hc.sl _) _ o hbs hlen consE ofE nilE str.toList 0 s8
      (by rw [List.drop_zero]; exact bytes_chars str) (Nat.zero_le _)) (fun sp s9 H5 hp5 => ?_)
  refine specR_pinAtI (C := ctxH C H5) (ctxOK_H hok _) PIN_STRING_OF_LIST (by decide) tcSl (by decide) ?_
  refine specR_pinXI (C := ctxH C H5) (ctxOK_H hok _) pinEmptyLevels 0 C.pins.emptyLevels _
    (fun s hp => pinEmptyLevels_run (C := ctxH C H5) (ctxOK_H hok _) hp) (pin_emptyLevels_cell (ctxOK_H hok H5)) tcE (by decide) ?_
  refine ILP.callE_spec (C := ctxH C H5) tcSlC fInternConst [lEn, lEus] [vv tcSl, vv tcE] constBody
    [_, Enc.idxW C.pins.emptyLevels] (by decide) rfl (by decide) hc.ic
    ⟨by first | (simp <;> rfl) | rfl, by first | (simp <;> rfl) | rfl, trivial⟩ (by exact const_body_spec ra (ctxH C H5) (ctxOK_H hok _) s9 _ _) (fun slC s10 => ?_)
  refine specR_congr (m' := internAppE slC sp >>= fun r => pure r) (by simp [internAppE]) ?_
  refine specR_internAppI (C := ctxH C H5) ra (ctxOK_H hok _) hc.sl.ia tcR (vv tcSlC) (vv tcSp) slC sp
    (by decide) (by simp) (by simp) (fun r s11 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨H5, hp1.trans (hp13.trans hp5), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Str
