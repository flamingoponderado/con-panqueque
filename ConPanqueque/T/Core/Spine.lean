import ConPanqueque.T.Core.WcStuck
import ConPanqueque.T.Ex.AppendFn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `getAppSpine`

The head, the argument vector and the spine's `app` nodes, in one walk: a recursive function answering a 3-cell
block `[head, args, nodes]` (each vector a heap block), built by appending.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.ExPre
open ConPanqueque.V.Enc

theorem getAppSpineGo_succ (fuel : Nat) (h : EIdx) : getAppSpineGo (fuel + 1) h =
    (if h.tag == ETag.app then (viewApp h >>= fun o => match o with
      | none => failDanglingE
      | some (f, a) => getAppSpineGo fuel f >>= fun t => pure (t.1, t.2.1.push a, t.2.2.push h))
    else pure (h, #[], #[])) := rfl


theorem viewApp_of_view {st : EStore} {i f a : EIdx}
    (htg : i.tag = ETag.app) (h : st.view i = some (.app f a)) : st.viewApp i = some (f, a) := by
  cases hc : st.viewApp i with
  | some p =>
    obtain ⟨f', a'⟩ := p
    have := ConRon.Bridge.view_of_viewApp htg hc
    rw [h] at this; cases this; rfl
  | none =>
    exfalso
    revert h hc
    simp only [EStore.view, EStore.viewApp, EStore.persGetApp]
    split <;> [skip; split] <;> simp [ETables.get, ETables.getApp, htg] <;>
      (simp only [show ETag.app ≠ ETag.bvar by decide, show ETag.app ≠ ETag.fvar by decide,
        show ETag.app ≠ ETag.sort by decide, show ETag.app ≠ ETag.const by decide, ite_false]; intro h1; split at h1 <;> simp_all <;> intro h2 <;> simp_all)


def gF := ofString "gsf"
def gH := ofString "gsh"
def gA := ofString "gsa"
def gB := ofString "gsb"
def gT := ofString "gst"
def gHd := ofString "gshd"
def gPa := ofString "gspa"
def gPn := ofString "gspn"
def gPa2 := ofString "gspa2"
def gPn2 := ofString "gspn2"
def gR := ofString "gsr"
def gE1 := ofString "gse1"
def gE2 := ofString "gse2"
def fGsp := ofString "getAppSpine"

@[simp] theorem gs_gF_ne_gH : gF ≠ gH := by decide
@[simp] theorem gs_gF_ne_gA : gF ≠ gA := by decide
@[simp] theorem gs_gF_ne_gB : gF ≠ gB := by decide
@[simp] theorem gs_gF_ne_gT : gF ≠ gT := by decide
@[simp] theorem gs_gF_ne_gHd : gF ≠ gHd := by decide
@[simp] theorem gs_gF_ne_gPa : gF ≠ gPa := by decide
@[simp] theorem gs_gF_ne_gPn : gF ≠ gPn := by decide
@[simp] theorem gs_gF_ne_gPa2 : gF ≠ gPa2 := by decide
@[simp] theorem gs_gF_ne_gPn2 : gF ≠ gPn2 := by decide
@[simp] theorem gs_gF_ne_gR : gF ≠ gR := by decide
@[simp] theorem gs_gF_ne_gE1 : gF ≠ gE1 := by decide
@[simp] theorem gs_gF_ne_gE2 : gF ≠ gE2 := by decide
@[simp] theorem gs_gF_ne_lFl : gF ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gF : lFl ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDh : gF ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gF : lDh ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDt : gF ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gF : lDt ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDg : gF ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gF : lDg ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDi : gF ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gF : lDi ≠ gF := by decide
@[simp] theorem gs_gF_ne_lRp : gF ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gF : lRp ≠ gF := by decide
@[simp] theorem gs_gF_ne_lRn : gF ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gF : lRn ≠ gF := by decide
@[simp] theorem gs_gF_ne_lFle : gF ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gF : lFle ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDir : gF ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gF : lDir ≠ gF := by decide
@[simp] theorem gs_gF_ne_lKb : gF ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gF : lKb ≠ gF := by decide
@[simp] theorem gs_gF_ne_lY : gF ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gF : ExS.lY ≠ gF := by decide
@[simp] theorem gs_gF_ne_aX : gF ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gF : ExPre.aX ≠ gF := by decide
@[simp] theorem gs_gF_ne_lCn : gF ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gF : lCn ≠ gF := by decide
@[simp] theorem gs_gF_ne_lW : gF ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gF : ExI.lW ≠ gF := by decide
@[simp] theorem gs_gF_ne_lSrc : gF ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gF : lSrc ≠ gF := by decide
@[simp] theorem gs_gF_ne_lDst : gF ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gF : lDst ≠ gF := by decide
@[simp] theorem gs_gF_ne_lCi : gF ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gF : lCi ≠ gF := by decide
@[simp] theorem gs_gF_ne_lCz : gF ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gF : lCz ≠ gF := by decide
@[simp] theorem gs_gH_ne_gF : gH ≠ gF := by decide
@[simp] theorem gs_gH_ne_gA : gH ≠ gA := by decide
@[simp] theorem gs_gH_ne_gB : gH ≠ gB := by decide
@[simp] theorem gs_gH_ne_gT : gH ≠ gT := by decide
@[simp] theorem gs_gH_ne_gHd : gH ≠ gHd := by decide
@[simp] theorem gs_gH_ne_gPa : gH ≠ gPa := by decide
@[simp] theorem gs_gH_ne_gPn : gH ≠ gPn := by decide
@[simp] theorem gs_gH_ne_gPa2 : gH ≠ gPa2 := by decide
@[simp] theorem gs_gH_ne_gPn2 : gH ≠ gPn2 := by decide
@[simp] theorem gs_gH_ne_gR : gH ≠ gR := by decide
@[simp] theorem gs_gH_ne_gE1 : gH ≠ gE1 := by decide
@[simp] theorem gs_gH_ne_gE2 : gH ≠ gE2 := by decide
@[simp] theorem gs_gH_ne_lFl : gH ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gH : lFl ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDh : gH ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gH : lDh ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDt : gH ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gH : lDt ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDg : gH ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gH : lDg ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDi : gH ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gH : lDi ≠ gH := by decide
@[simp] theorem gs_gH_ne_lRp : gH ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gH : lRp ≠ gH := by decide
@[simp] theorem gs_gH_ne_lRn : gH ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gH : lRn ≠ gH := by decide
@[simp] theorem gs_gH_ne_lFle : gH ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gH : lFle ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDir : gH ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gH : lDir ≠ gH := by decide
@[simp] theorem gs_gH_ne_lKb : gH ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gH : lKb ≠ gH := by decide
@[simp] theorem gs_gH_ne_lY : gH ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gH : ExS.lY ≠ gH := by decide
@[simp] theorem gs_gH_ne_aX : gH ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gH : ExPre.aX ≠ gH := by decide
@[simp] theorem gs_gH_ne_lCn : gH ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gH : lCn ≠ gH := by decide
@[simp] theorem gs_gH_ne_lW : gH ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gH : ExI.lW ≠ gH := by decide
@[simp] theorem gs_gH_ne_lSrc : gH ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gH : lSrc ≠ gH := by decide
@[simp] theorem gs_gH_ne_lDst : gH ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gH : lDst ≠ gH := by decide
@[simp] theorem gs_gH_ne_lCi : gH ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gH : lCi ≠ gH := by decide
@[simp] theorem gs_gH_ne_lCz : gH ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gH : lCz ≠ gH := by decide
@[simp] theorem gs_gA_ne_gF : gA ≠ gF := by decide
@[simp] theorem gs_gA_ne_gH : gA ≠ gH := by decide
@[simp] theorem gs_gA_ne_gB : gA ≠ gB := by decide
@[simp] theorem gs_gA_ne_gT : gA ≠ gT := by decide
@[simp] theorem gs_gA_ne_gHd : gA ≠ gHd := by decide
@[simp] theorem gs_gA_ne_gPa : gA ≠ gPa := by decide
@[simp] theorem gs_gA_ne_gPn : gA ≠ gPn := by decide
@[simp] theorem gs_gA_ne_gPa2 : gA ≠ gPa2 := by decide
@[simp] theorem gs_gA_ne_gPn2 : gA ≠ gPn2 := by decide
@[simp] theorem gs_gA_ne_gR : gA ≠ gR := by decide
@[simp] theorem gs_gA_ne_gE1 : gA ≠ gE1 := by decide
@[simp] theorem gs_gA_ne_gE2 : gA ≠ gE2 := by decide
@[simp] theorem gs_gA_ne_lFl : gA ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gA : lFl ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDh : gA ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gA : lDh ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDt : gA ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gA : lDt ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDg : gA ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gA : lDg ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDi : gA ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gA : lDi ≠ gA := by decide
@[simp] theorem gs_gA_ne_lRp : gA ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gA : lRp ≠ gA := by decide
@[simp] theorem gs_gA_ne_lRn : gA ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gA : lRn ≠ gA := by decide
@[simp] theorem gs_gA_ne_lFle : gA ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gA : lFle ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDir : gA ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gA : lDir ≠ gA := by decide
@[simp] theorem gs_gA_ne_lKb : gA ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gA : lKb ≠ gA := by decide
@[simp] theorem gs_gA_ne_lY : gA ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gA : ExS.lY ≠ gA := by decide
@[simp] theorem gs_gA_ne_aX : gA ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gA : ExPre.aX ≠ gA := by decide
@[simp] theorem gs_gA_ne_lCn : gA ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gA : lCn ≠ gA := by decide
@[simp] theorem gs_gA_ne_lW : gA ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gA : ExI.lW ≠ gA := by decide
@[simp] theorem gs_gA_ne_lSrc : gA ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gA : lSrc ≠ gA := by decide
@[simp] theorem gs_gA_ne_lDst : gA ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gA : lDst ≠ gA := by decide
@[simp] theorem gs_gA_ne_lCi : gA ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gA : lCi ≠ gA := by decide
@[simp] theorem gs_gA_ne_lCz : gA ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gA : lCz ≠ gA := by decide
@[simp] theorem gs_gB_ne_gF : gB ≠ gF := by decide
@[simp] theorem gs_gB_ne_gH : gB ≠ gH := by decide
@[simp] theorem gs_gB_ne_gA : gB ≠ gA := by decide
@[simp] theorem gs_gB_ne_gT : gB ≠ gT := by decide
@[simp] theorem gs_gB_ne_gHd : gB ≠ gHd := by decide
@[simp] theorem gs_gB_ne_gPa : gB ≠ gPa := by decide
@[simp] theorem gs_gB_ne_gPn : gB ≠ gPn := by decide
@[simp] theorem gs_gB_ne_gPa2 : gB ≠ gPa2 := by decide
@[simp] theorem gs_gB_ne_gPn2 : gB ≠ gPn2 := by decide
@[simp] theorem gs_gB_ne_gR : gB ≠ gR := by decide
@[simp] theorem gs_gB_ne_gE1 : gB ≠ gE1 := by decide
@[simp] theorem gs_gB_ne_gE2 : gB ≠ gE2 := by decide
@[simp] theorem gs_gB_ne_lFl : gB ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gB : lFl ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDh : gB ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gB : lDh ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDt : gB ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gB : lDt ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDg : gB ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gB : lDg ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDi : gB ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gB : lDi ≠ gB := by decide
@[simp] theorem gs_gB_ne_lRp : gB ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gB : lRp ≠ gB := by decide
@[simp] theorem gs_gB_ne_lRn : gB ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gB : lRn ≠ gB := by decide
@[simp] theorem gs_gB_ne_lFle : gB ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gB : lFle ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDir : gB ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gB : lDir ≠ gB := by decide
@[simp] theorem gs_gB_ne_lKb : gB ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gB : lKb ≠ gB := by decide
@[simp] theorem gs_gB_ne_lY : gB ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gB : ExS.lY ≠ gB := by decide
@[simp] theorem gs_gB_ne_aX : gB ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gB : ExPre.aX ≠ gB := by decide
@[simp] theorem gs_gB_ne_lCn : gB ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gB : lCn ≠ gB := by decide
@[simp] theorem gs_gB_ne_lW : gB ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gB : ExI.lW ≠ gB := by decide
@[simp] theorem gs_gB_ne_lSrc : gB ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gB : lSrc ≠ gB := by decide
@[simp] theorem gs_gB_ne_lDst : gB ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gB : lDst ≠ gB := by decide
@[simp] theorem gs_gB_ne_lCi : gB ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gB : lCi ≠ gB := by decide
@[simp] theorem gs_gB_ne_lCz : gB ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gB : lCz ≠ gB := by decide
@[simp] theorem gs_gT_ne_gF : gT ≠ gF := by decide
@[simp] theorem gs_gT_ne_gH : gT ≠ gH := by decide
@[simp] theorem gs_gT_ne_gA : gT ≠ gA := by decide
@[simp] theorem gs_gT_ne_gB : gT ≠ gB := by decide
@[simp] theorem gs_gT_ne_gHd : gT ≠ gHd := by decide
@[simp] theorem gs_gT_ne_gPa : gT ≠ gPa := by decide
@[simp] theorem gs_gT_ne_gPn : gT ≠ gPn := by decide
@[simp] theorem gs_gT_ne_gPa2 : gT ≠ gPa2 := by decide
@[simp] theorem gs_gT_ne_gPn2 : gT ≠ gPn2 := by decide
@[simp] theorem gs_gT_ne_gR : gT ≠ gR := by decide
@[simp] theorem gs_gT_ne_gE1 : gT ≠ gE1 := by decide
@[simp] theorem gs_gT_ne_gE2 : gT ≠ gE2 := by decide
@[simp] theorem gs_gT_ne_lFl : gT ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gT : lFl ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDh : gT ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gT : lDh ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDt : gT ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gT : lDt ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDg : gT ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gT : lDg ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDi : gT ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gT : lDi ≠ gT := by decide
@[simp] theorem gs_gT_ne_lRp : gT ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gT : lRp ≠ gT := by decide
@[simp] theorem gs_gT_ne_lRn : gT ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gT : lRn ≠ gT := by decide
@[simp] theorem gs_gT_ne_lFle : gT ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gT : lFle ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDir : gT ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gT : lDir ≠ gT := by decide
@[simp] theorem gs_gT_ne_lKb : gT ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gT : lKb ≠ gT := by decide
@[simp] theorem gs_gT_ne_lY : gT ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gT : ExS.lY ≠ gT := by decide
@[simp] theorem gs_gT_ne_aX : gT ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gT : ExPre.aX ≠ gT := by decide
@[simp] theorem gs_gT_ne_lCn : gT ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gT : lCn ≠ gT := by decide
@[simp] theorem gs_gT_ne_lW : gT ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gT : ExI.lW ≠ gT := by decide
@[simp] theorem gs_gT_ne_lSrc : gT ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gT : lSrc ≠ gT := by decide
@[simp] theorem gs_gT_ne_lDst : gT ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gT : lDst ≠ gT := by decide
@[simp] theorem gs_gT_ne_lCi : gT ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gT : lCi ≠ gT := by decide
@[simp] theorem gs_gT_ne_lCz : gT ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gT : lCz ≠ gT := by decide
@[simp] theorem gs_gHd_ne_gF : gHd ≠ gF := by decide
@[simp] theorem gs_gHd_ne_gH : gHd ≠ gH := by decide
@[simp] theorem gs_gHd_ne_gA : gHd ≠ gA := by decide
@[simp] theorem gs_gHd_ne_gB : gHd ≠ gB := by decide
@[simp] theorem gs_gHd_ne_gT : gHd ≠ gT := by decide
@[simp] theorem gs_gHd_ne_gPa : gHd ≠ gPa := by decide
@[simp] theorem gs_gHd_ne_gPn : gHd ≠ gPn := by decide
@[simp] theorem gs_gHd_ne_gPa2 : gHd ≠ gPa2 := by decide
@[simp] theorem gs_gHd_ne_gPn2 : gHd ≠ gPn2 := by decide
@[simp] theorem gs_gHd_ne_gR : gHd ≠ gR := by decide
@[simp] theorem gs_gHd_ne_gE1 : gHd ≠ gE1 := by decide
@[simp] theorem gs_gHd_ne_gE2 : gHd ≠ gE2 := by decide
@[simp] theorem gs_gHd_ne_lFl : gHd ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gHd : lFl ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDh : gHd ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gHd : lDh ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDt : gHd ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gHd : lDt ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDg : gHd ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gHd : lDg ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDi : gHd ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gHd : lDi ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lRp : gHd ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gHd : lRp ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lRn : gHd ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gHd : lRn ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lFle : gHd ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gHd : lFle ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDir : gHd ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gHd : lDir ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lKb : gHd ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gHd : lKb ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lY : gHd ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gHd : ExS.lY ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_aX : gHd ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gHd : ExPre.aX ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lCn : gHd ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gHd : lCn ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lW : gHd ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gHd : ExI.lW ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lSrc : gHd ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gHd : lSrc ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lDst : gHd ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gHd : lDst ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lCi : gHd ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gHd : lCi ≠ gHd := by decide
@[simp] theorem gs_gHd_ne_lCz : gHd ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gHd : lCz ≠ gHd := by decide
@[simp] theorem gs_gPa_ne_gF : gPa ≠ gF := by decide
@[simp] theorem gs_gPa_ne_gH : gPa ≠ gH := by decide
@[simp] theorem gs_gPa_ne_gA : gPa ≠ gA := by decide
@[simp] theorem gs_gPa_ne_gB : gPa ≠ gB := by decide
@[simp] theorem gs_gPa_ne_gT : gPa ≠ gT := by decide
@[simp] theorem gs_gPa_ne_gHd : gPa ≠ gHd := by decide
@[simp] theorem gs_gPa_ne_gPn : gPa ≠ gPn := by decide
@[simp] theorem gs_gPa_ne_gPa2 : gPa ≠ gPa2 := by decide
@[simp] theorem gs_gPa_ne_gPn2 : gPa ≠ gPn2 := by decide
@[simp] theorem gs_gPa_ne_gR : gPa ≠ gR := by decide
@[simp] theorem gs_gPa_ne_gE1 : gPa ≠ gE1 := by decide
@[simp] theorem gs_gPa_ne_gE2 : gPa ≠ gE2 := by decide
@[simp] theorem gs_gPa_ne_lFl : gPa ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gPa : lFl ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDh : gPa ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gPa : lDh ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDt : gPa ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gPa : lDt ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDg : gPa ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gPa : lDg ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDi : gPa ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gPa : lDi ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lRp : gPa ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gPa : lRp ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lRn : gPa ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gPa : lRn ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lFle : gPa ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gPa : lFle ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDir : gPa ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gPa : lDir ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lKb : gPa ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gPa : lKb ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lY : gPa ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gPa : ExS.lY ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_aX : gPa ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gPa : ExPre.aX ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lCn : gPa ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gPa : lCn ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lW : gPa ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gPa : ExI.lW ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lSrc : gPa ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gPa : lSrc ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lDst : gPa ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gPa : lDst ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lCi : gPa ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gPa : lCi ≠ gPa := by decide
@[simp] theorem gs_gPa_ne_lCz : gPa ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gPa : lCz ≠ gPa := by decide
@[simp] theorem gs_gPn_ne_gF : gPn ≠ gF := by decide
@[simp] theorem gs_gPn_ne_gH : gPn ≠ gH := by decide
@[simp] theorem gs_gPn_ne_gA : gPn ≠ gA := by decide
@[simp] theorem gs_gPn_ne_gB : gPn ≠ gB := by decide
@[simp] theorem gs_gPn_ne_gT : gPn ≠ gT := by decide
@[simp] theorem gs_gPn_ne_gHd : gPn ≠ gHd := by decide
@[simp] theorem gs_gPn_ne_gPa : gPn ≠ gPa := by decide
@[simp] theorem gs_gPn_ne_gPa2 : gPn ≠ gPa2 := by decide
@[simp] theorem gs_gPn_ne_gPn2 : gPn ≠ gPn2 := by decide
@[simp] theorem gs_gPn_ne_gR : gPn ≠ gR := by decide
@[simp] theorem gs_gPn_ne_gE1 : gPn ≠ gE1 := by decide
@[simp] theorem gs_gPn_ne_gE2 : gPn ≠ gE2 := by decide
@[simp] theorem gs_gPn_ne_lFl : gPn ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gPn : lFl ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDh : gPn ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gPn : lDh ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDt : gPn ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gPn : lDt ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDg : gPn ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gPn : lDg ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDi : gPn ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gPn : lDi ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lRp : gPn ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gPn : lRp ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lRn : gPn ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gPn : lRn ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lFle : gPn ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gPn : lFle ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDir : gPn ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gPn : lDir ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lKb : gPn ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gPn : lKb ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lY : gPn ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gPn : ExS.lY ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_aX : gPn ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gPn : ExPre.aX ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lCn : gPn ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gPn : lCn ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lW : gPn ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gPn : ExI.lW ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lSrc : gPn ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gPn : lSrc ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lDst : gPn ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gPn : lDst ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lCi : gPn ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gPn : lCi ≠ gPn := by decide
@[simp] theorem gs_gPn_ne_lCz : gPn ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gPn : lCz ≠ gPn := by decide
@[simp] theorem gs_gPa2_ne_gF : gPa2 ≠ gF := by decide
@[simp] theorem gs_gPa2_ne_gH : gPa2 ≠ gH := by decide
@[simp] theorem gs_gPa2_ne_gA : gPa2 ≠ gA := by decide
@[simp] theorem gs_gPa2_ne_gB : gPa2 ≠ gB := by decide
@[simp] theorem gs_gPa2_ne_gT : gPa2 ≠ gT := by decide
@[simp] theorem gs_gPa2_ne_gHd : gPa2 ≠ gHd := by decide
@[simp] theorem gs_gPa2_ne_gPa : gPa2 ≠ gPa := by decide
@[simp] theorem gs_gPa2_ne_gPn : gPa2 ≠ gPn := by decide
@[simp] theorem gs_gPa2_ne_gPn2 : gPa2 ≠ gPn2 := by decide
@[simp] theorem gs_gPa2_ne_gR : gPa2 ≠ gR := by decide
@[simp] theorem gs_gPa2_ne_gE1 : gPa2 ≠ gE1 := by decide
@[simp] theorem gs_gPa2_ne_gE2 : gPa2 ≠ gE2 := by decide
@[simp] theorem gs_gPa2_ne_lFl : gPa2 ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gPa2 : lFl ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDh : gPa2 ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gPa2 : lDh ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDt : gPa2 ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gPa2 : lDt ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDg : gPa2 ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gPa2 : lDg ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDi : gPa2 ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gPa2 : lDi ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lRp : gPa2 ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gPa2 : lRp ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lRn : gPa2 ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gPa2 : lRn ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lFle : gPa2 ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gPa2 : lFle ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDir : gPa2 ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gPa2 : lDir ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lKb : gPa2 ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gPa2 : lKb ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lY : gPa2 ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gPa2 : ExS.lY ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_aX : gPa2 ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gPa2 : ExPre.aX ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lCn : gPa2 ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gPa2 : lCn ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lW : gPa2 ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gPa2 : ExI.lW ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lSrc : gPa2 ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gPa2 : lSrc ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lDst : gPa2 ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gPa2 : lDst ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lCi : gPa2 ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gPa2 : lCi ≠ gPa2 := by decide
@[simp] theorem gs_gPa2_ne_lCz : gPa2 ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gPa2 : lCz ≠ gPa2 := by decide
@[simp] theorem gs_gPn2_ne_gF : gPn2 ≠ gF := by decide
@[simp] theorem gs_gPn2_ne_gH : gPn2 ≠ gH := by decide
@[simp] theorem gs_gPn2_ne_gA : gPn2 ≠ gA := by decide
@[simp] theorem gs_gPn2_ne_gB : gPn2 ≠ gB := by decide
@[simp] theorem gs_gPn2_ne_gT : gPn2 ≠ gT := by decide
@[simp] theorem gs_gPn2_ne_gHd : gPn2 ≠ gHd := by decide
@[simp] theorem gs_gPn2_ne_gPa : gPn2 ≠ gPa := by decide
@[simp] theorem gs_gPn2_ne_gPn : gPn2 ≠ gPn := by decide
@[simp] theorem gs_gPn2_ne_gPa2 : gPn2 ≠ gPa2 := by decide
@[simp] theorem gs_gPn2_ne_gR : gPn2 ≠ gR := by decide
@[simp] theorem gs_gPn2_ne_gE1 : gPn2 ≠ gE1 := by decide
@[simp] theorem gs_gPn2_ne_gE2 : gPn2 ≠ gE2 := by decide
@[simp] theorem gs_gPn2_ne_lFl : gPn2 ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gPn2 : lFl ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDh : gPn2 ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gPn2 : lDh ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDt : gPn2 ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gPn2 : lDt ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDg : gPn2 ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gPn2 : lDg ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDi : gPn2 ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gPn2 : lDi ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lRp : gPn2 ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gPn2 : lRp ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lRn : gPn2 ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gPn2 : lRn ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lFle : gPn2 ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gPn2 : lFle ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDir : gPn2 ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gPn2 : lDir ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lKb : gPn2 ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gPn2 : lKb ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lY : gPn2 ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gPn2 : ExS.lY ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_aX : gPn2 ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gPn2 : ExPre.aX ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lCn : gPn2 ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gPn2 : lCn ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lW : gPn2 ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gPn2 : ExI.lW ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lSrc : gPn2 ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gPn2 : lSrc ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lDst : gPn2 ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gPn2 : lDst ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lCi : gPn2 ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gPn2 : lCi ≠ gPn2 := by decide
@[simp] theorem gs_gPn2_ne_lCz : gPn2 ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gPn2 : lCz ≠ gPn2 := by decide
@[simp] theorem gs_gR_ne_gF : gR ≠ gF := by decide
@[simp] theorem gs_gR_ne_gH : gR ≠ gH := by decide
@[simp] theorem gs_gR_ne_gA : gR ≠ gA := by decide
@[simp] theorem gs_gR_ne_gB : gR ≠ gB := by decide
@[simp] theorem gs_gR_ne_gT : gR ≠ gT := by decide
@[simp] theorem gs_gR_ne_gHd : gR ≠ gHd := by decide
@[simp] theorem gs_gR_ne_gPa : gR ≠ gPa := by decide
@[simp] theorem gs_gR_ne_gPn : gR ≠ gPn := by decide
@[simp] theorem gs_gR_ne_gPa2 : gR ≠ gPa2 := by decide
@[simp] theorem gs_gR_ne_gPn2 : gR ≠ gPn2 := by decide
@[simp] theorem gs_gR_ne_gE1 : gR ≠ gE1 := by decide
@[simp] theorem gs_gR_ne_gE2 : gR ≠ gE2 := by decide
@[simp] theorem gs_gR_ne_lFl : gR ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gR : lFl ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDh : gR ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gR : lDh ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDt : gR ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gR : lDt ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDg : gR ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gR : lDg ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDi : gR ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gR : lDi ≠ gR := by decide
@[simp] theorem gs_gR_ne_lRp : gR ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gR : lRp ≠ gR := by decide
@[simp] theorem gs_gR_ne_lRn : gR ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gR : lRn ≠ gR := by decide
@[simp] theorem gs_gR_ne_lFle : gR ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gR : lFle ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDir : gR ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gR : lDir ≠ gR := by decide
@[simp] theorem gs_gR_ne_lKb : gR ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gR : lKb ≠ gR := by decide
@[simp] theorem gs_gR_ne_lY : gR ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gR : ExS.lY ≠ gR := by decide
@[simp] theorem gs_gR_ne_aX : gR ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gR : ExPre.aX ≠ gR := by decide
@[simp] theorem gs_gR_ne_lCn : gR ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gR : lCn ≠ gR := by decide
@[simp] theorem gs_gR_ne_lW : gR ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gR : ExI.lW ≠ gR := by decide
@[simp] theorem gs_gR_ne_lSrc : gR ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gR : lSrc ≠ gR := by decide
@[simp] theorem gs_gR_ne_lDst : gR ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gR : lDst ≠ gR := by decide
@[simp] theorem gs_gR_ne_lCi : gR ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gR : lCi ≠ gR := by decide
@[simp] theorem gs_gR_ne_lCz : gR ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gR : lCz ≠ gR := by decide
@[simp] theorem gs_gE1_ne_gF : gE1 ≠ gF := by decide
@[simp] theorem gs_gE1_ne_gH : gE1 ≠ gH := by decide
@[simp] theorem gs_gE1_ne_gA : gE1 ≠ gA := by decide
@[simp] theorem gs_gE1_ne_gB : gE1 ≠ gB := by decide
@[simp] theorem gs_gE1_ne_gT : gE1 ≠ gT := by decide
@[simp] theorem gs_gE1_ne_gHd : gE1 ≠ gHd := by decide
@[simp] theorem gs_gE1_ne_gPa : gE1 ≠ gPa := by decide
@[simp] theorem gs_gE1_ne_gPn : gE1 ≠ gPn := by decide
@[simp] theorem gs_gE1_ne_gPa2 : gE1 ≠ gPa2 := by decide
@[simp] theorem gs_gE1_ne_gPn2 : gE1 ≠ gPn2 := by decide
@[simp] theorem gs_gE1_ne_gR : gE1 ≠ gR := by decide
@[simp] theorem gs_gE1_ne_gE2 : gE1 ≠ gE2 := by decide
@[simp] theorem gs_gE1_ne_lFl : gE1 ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gE1 : lFl ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDh : gE1 ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gE1 : lDh ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDt : gE1 ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gE1 : lDt ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDg : gE1 ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gE1 : lDg ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDi : gE1 ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gE1 : lDi ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lRp : gE1 ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gE1 : lRp ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lRn : gE1 ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gE1 : lRn ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lFle : gE1 ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gE1 : lFle ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDir : gE1 ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gE1 : lDir ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lKb : gE1 ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gE1 : lKb ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lY : gE1 ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gE1 : ExS.lY ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_aX : gE1 ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gE1 : ExPre.aX ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lCn : gE1 ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gE1 : lCn ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lW : gE1 ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gE1 : ExI.lW ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lSrc : gE1 ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gE1 : lSrc ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lDst : gE1 ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gE1 : lDst ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lCi : gE1 ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gE1 : lCi ≠ gE1 := by decide
@[simp] theorem gs_gE1_ne_lCz : gE1 ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gE1 : lCz ≠ gE1 := by decide
@[simp] theorem gs_gE2_ne_gF : gE2 ≠ gF := by decide
@[simp] theorem gs_gE2_ne_gH : gE2 ≠ gH := by decide
@[simp] theorem gs_gE2_ne_gA : gE2 ≠ gA := by decide
@[simp] theorem gs_gE2_ne_gB : gE2 ≠ gB := by decide
@[simp] theorem gs_gE2_ne_gT : gE2 ≠ gT := by decide
@[simp] theorem gs_gE2_ne_gHd : gE2 ≠ gHd := by decide
@[simp] theorem gs_gE2_ne_gPa : gE2 ≠ gPa := by decide
@[simp] theorem gs_gE2_ne_gPn : gE2 ≠ gPn := by decide
@[simp] theorem gs_gE2_ne_gPa2 : gE2 ≠ gPa2 := by decide
@[simp] theorem gs_gE2_ne_gPn2 : gE2 ≠ gPn2 := by decide
@[simp] theorem gs_gE2_ne_gR : gE2 ≠ gR := by decide
@[simp] theorem gs_gE2_ne_gE1 : gE2 ≠ gE1 := by decide
@[simp] theorem gs_gE2_ne_lFl : gE2 ≠ lFl := by decide
@[simp] theorem gs_lFl_ne_gE2 : lFl ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDh : gE2 ≠ lDh := by decide
@[simp] theorem gs_lDh_ne_gE2 : lDh ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDt : gE2 ≠ lDt := by decide
@[simp] theorem gs_lDt_ne_gE2 : lDt ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDg : gE2 ≠ lDg := by decide
@[simp] theorem gs_lDg_ne_gE2 : lDg ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDi : gE2 ≠ lDi := by decide
@[simp] theorem gs_lDi_ne_gE2 : lDi ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lRp : gE2 ≠ lRp := by decide
@[simp] theorem gs_lRp_ne_gE2 : lRp ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lRn : gE2 ≠ lRn := by decide
@[simp] theorem gs_lRn_ne_gE2 : lRn ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lFle : gE2 ≠ lFle := by decide
@[simp] theorem gs_lFle_ne_gE2 : lFle ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDir : gE2 ≠ lDir := by decide
@[simp] theorem gs_lDir_ne_gE2 : lDir ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lKb : gE2 ≠ lKb := by decide
@[simp] theorem gs_lKb_ne_gE2 : lKb ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lY : gE2 ≠ ExS.lY := by decide
@[simp] theorem gs_lY_ne_gE2 : ExS.lY ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_aX : gE2 ≠ ExPre.aX := by decide
@[simp] theorem gs_aX_ne_gE2 : ExPre.aX ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lCn : gE2 ≠ lCn := by decide
@[simp] theorem gs_lCn_ne_gE2 : lCn ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lW : gE2 ≠ ExI.lW := by decide
@[simp] theorem gs_lW_ne_gE2 : ExI.lW ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lSrc : gE2 ≠ lSrc := by decide
@[simp] theorem gs_lSrc_ne_gE2 : lSrc ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lDst : gE2 ≠ lDst := by decide
@[simp] theorem gs_lDst_ne_gE2 : lDst ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lCi : gE2 ≠ lCi := by decide
@[simp] theorem gs_lCi_ne_gE2 : lCi ≠ gE2 := by decide
@[simp] theorem gs_gE2_ne_lCz : gE2 ≠ lCz := by decide
@[simp] theorem gs_lCz_ne_gE2 : lCz ≠ gE2 := by decide

def gspParams : List MlS := [gF, gH]
def gspLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, gA, gB, gT, gHd, gPa, gPn, gPa2, gPn2, gR, gE1, gE2]

def gspCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv gF) (.const 0)) hang
  (.ite (tagIs4E gH)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv gH)) (.seq eViewP
    (.seq (.assign .local gA (.load .one (vv lRp))) (.seq (.assign .local gB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, gT), none)) fGsp [.op .sub [vv gF, .const 1], vv gA])
    (.seq (.assign .local gHd (.load .one (vv gT)))
    (.seq (.assign .local gPa (.load .one (.op .add [vv gT, .const 8])))
    (.seq (.assign .local gPn (.load .one (.op .add [vv gT, .const 16])))
    (.seq (.call (some (some (.local, gPa2), none)) fAppend [vv gPa, vv gB])
    (.seq (.call (some (some (.local, gPn2), none)) fAppend [vv gPn, vv gH])
    (allocP C gR (.const 24) (.seq (.store (vv gR) (vv gHd))
    (.seq (.store (.op .add [vv gR, .const 8]) (vv gPa2))
    (.seq (.store (.op .add [vv gR, .const 16]) (vv gPn2)) (.return (vv gR)))))))))))))))))
    (allocP C gE1 (.const 8) (.seq (.store (vv gE1) (.const 0))
    (allocP C gE2 (.const 8) (.seq (.store (vv gE2) (.const 0))
    (allocP C gR (.const 24) (.seq (.store (vv gR) (vv gH))
    (.seq (.store (.op .add [vv gR, .const 8]) (vv gE1))
    (.seq (.store (.op .add [vv gR, .const 16]) (vv gE2)) (.return (vv gR)))))))))))

def gspBody (C : Ctx) : ProgHOL 64 := prologue gspLocals (gspCore C)


section
variable {σ : Type}

def PostSp (C : Ctx) (s : AState) (r : EIdx × Array EIdx × Array EIdx) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o pa pn, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (Enc.idxW r.1) ∧
    H'[o + 1]? = some (cellA C pa) ∧ H'[o + 2]? = some (cellA C pn) ∧
    BlkAt H' pa (r.2.1.toList.map Enc.idxW) ∧ BlkAt H' pn (r.2.2.toList.map Enc.idxW) ∧ SR (ctxH C H') s' st

theorem postSp_locals (C : Ctx) (s : AState) : ∀ (a : EIdx × Array EIdx × Array EIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostSp C s a w s' st → PostSp C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, pa, pn, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
    ⟨h1, H', o, pa, pn, h2, h3, h4, h5, h6, h7, h8, sr_of_eq h9 rfl rfl rfl rfl⟩

theorem gsp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gspLocals → (ctxEnv C ++ gspParams.zip vals).get x = none :=
  Knot.params_none C gspLocals gspParams vals (by decide) (by decide)

/-- An empty block in `x`. -/
theorem specR_emptyBlk {α : Type} {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (hx : x ∈ D)
    (hk : ∀ (H' : List (BitVec 64)) o, H <+: H' → BlkAt H' o [] →
      SpecR (Inv (ctxH C0 H') s ((x, cellA C0 o) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C0 H) s Γ [] D) (allocP C0 x (.const 8) (.seq (.store (vv x) (.const 0)) rest)) s m R := by
  refine specR_allocI (C := ctxH C0 H) x (.const 8) 1 (by norm_num) hx (fun v => by simp [sev])
    (fun H1 ws hp1 hwl _ => ?_)
  have hj : H1.length < (ctxH (ctxH C0 H) (H1 ++ ws)).H.length := by show _ < (H1 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) (.const 0) _ hj 0 (by simp; rfl) rfl ?_
  refine hk _ H1.length (hp1.trans (prefix_set_ge (List.prefix_append _ ws) _ (Nat.le_refl _) 0)) ⟨?_, fun i hi => ?_⟩
  · show ((H1 ++ ws).set H1.length 0)[H1.length]? = _
    rw [List.getElem?_set_self (by simp; omega)]; rfl
  · simp at hi

/-- Allocate `[a, b, c]` and return it. -/
theorem specR_tripRet {C0 : Ctx} (hok : CtxOK C0) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {D : List MlS} {r : EIdx × Array EIdx × Array EIdx} (x xa xb xc : MlS) (pa pn : Nat)
    (hx : x ∈ D) (hne : xa ≠ x ∧ xb ≠ x ∧ xc ≠ x)
    (ha : Γ.get xa = some (Enc.idxW r.1)) (hb : Γ.get xb = some (cellA C0 pa)) (hc : Γ.get xc = some (cellA C0 pn))
    (hpre : C0.H <+: H) (hba : BlkAt H pa (r.2.1.toList.map Enc.idxW)) (hbn : BlkAt H pn (r.2.2.toList.map Enc.idxW)) :
    SpecR (σ := σ) (Inv (ctxH C0 H) s Γ [] D)
      (allocP C0 x (.const 24) (.seq (.store (vv x) (vv xa))
        (.seq (.store (.op .add [vv x, .const 8]) (vv xb))
        (.seq (.store (.op .add [vv x, .const 16]) (vv xc)) (.return (vv x)))))) s (pure r) (PostSp C0 s) := by
  obtain ⟨h1, h2, h3⟩ := hne
  refine specR_allocI (C := ctxH C0 H) x (.const 24) 3 (by norm_num) hx (fun v => by simp [sev])
    (fun H1 ws hp1 hwl _ => ?_)
  have hj : H1.length < (ctxH (ctxH C0 H) (H1 ++ ws)).H.length := by show _ < (H1 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) (vv xa) _ hj (Enc.idxW r.1) (by simp; rfl) (by simp [h1, ha]) ?_
  have hj2 : H1.length + 1 < (ctxH (ctxH C0 H) ((H1 ++ ws).set H1.length (Enc.idxW r.1))).H.length := by
    show _ < ((H1 ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (vv xb) _ hj2 (cellA C0 pa) (by simp [sev]; exact cellA_add8 C0 _)
    (by simp [h2, hb]) ?_
  have hj3 : H1.length + 2 < (ctxH (ctxH C0 H) (((H1 ++ ws).set H1.length (Enc.idxW r.1)).set (H1.length + 1)
      (cellA C0 pa))).H.length := by
    show _ < (((H1 ++ ws).set _ _).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (vv xc) _ hj3 (cellA C0 pn)
    (by simp [sev]; rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl]; exact ExPre.cellA_off C0 _ 2)
    (by simp [h3, hc]) ?_
  refine specR_returnI _ (cellA C0 H1.length) (by simp; rfl) (fun t ht => ?_)
  let G := (((H1 ++ ws).set H1.length (Enc.idxW r.1)).set (H1.length + 1) (cellA C0 pa)).set (H1.length + 2)
    (cellA C0 pn)
  have hpl := hp1.length_le
  have hpG : H1 <+: G := prefix_set_ge (prefix_set_ge (prefix_set_ge (List.prefix_append _ ws) _ (Nat.le_refl _) _)
    _ (by simp) _) _ (by simp) _
  refine ⟨rfl, G, H1.length, pa, pn, hpre.trans (hp1.trans hpG), rfl, ?_, ?_, ?_, blkAt_mono hba (hp1.trans hpG),
    blkAt_mono hbn (hp1.trans hpG), sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · show ((((H1 ++ ws).set _ _).set _ _).set _ _)[H1.length]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  · show ((((H1 ++ ws).set _ _).set _ _).set _ _)[H1.length + 1]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  · show ((((H1 ++ ws).set _ _).set _ _).set _ _)[H1.length + 2]? = _
    rw [List.getElem?_set_self (by simp; omega)]

end


section
variable {σ : Type}

theorem viewApp_run (h : EIdx) (s : AState) : viewApp h s = .ok (s.store.viewApp h, s) := rfl

theorem gsp_spec (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fGsp = some (gspParams.map (fun p => (p, ShapeHOL.one)), gspBody C, .one))
    (hca : C.code.lookup fAppend = some (appParams.map (fun p => (p, ShapeHOL.one)), appBody C, .one)) :
    ∀ fuel, fuel < 2 ^ 64 → ∀ (H : List (BitVec 64)) s h, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (gspParams.zip [BitVec.ofNat 64 fuel, Enc.idxW h])) (gspBody C) s
        (getAppSpineGo fuel h) (PostSp (ctxH C H) s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ H s h _
    refine specR_prologue (postSp_locals _ s) (gsp_none _ _) ?_
    unfold gspCore
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, gspParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ f ih =>
    intro hf H s h hpre
    have hok' := ctxOK_H hok H
    refine specR_prologue (postSp_locals _ s) (gsp_none _ _) ?_
    unfold gspCore
    have hfw : BitVec.ofNat 64 (f + 1) ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
    have hc0 : sev (ctxEnv (ctxH C H) ++ gspParams.zip [BitVec.ofNat 64 (f + 1), Enc.idxW h])
        (.cmp .equal (vv gF) (.const 0)) = some 0 := by
      simp +decide [sev, Env.get, gspParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hfw
    refine specR_ifI _ 0 hc0 (fun h => absurd rfl h) (fun _ => ?_)
    rw [getAppSpineGo_succ]
    have hT := sev_tagIs4B (ctxEnv (ctxH C H) ++ gspParams.zip [BitVec.ofNat 64 (f + 1), Enc.idxW h]) gH h
      (by simp +decide [Env.get, gspParams, ctxEnv])
    by_cases ht : (h.tag == 4) = true
    · rw [ite_eq_left (show (h.tag == ETag.app) = true from ht)]
      refine specR_ifI _ 1 (by rw [hT, ht]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]; rfl) ?_
      refine specR_assignI lDh (vv gH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, gspParams, ctxEnv]) ?_
      refine specR_viewP h (by simp) (by simp +decide [Env.get]; rfl) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v P hv htn _ => ?_)
      have htg : h.tag = 4 := by simpa using ht
      have h4 : v.tagN = 4 := by rw [htn, htg]; rfl
      obtain ⟨fn, a, rfl⟩ := tagN_app h4
      have hva : s.store.viewApp h = some (fn, a) := viewApp_of_view (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewApp_run, hva]) ?_
      refine specR_loadI' gA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW fn) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW fn) [Enc.idxW a] []) ?_
      refine specR_loadI' gB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW fn) (Enc.idxW a) [] []) ?_
      refine specR_dropM ?_
      refine specR_callNIH (C := ctxH C H) gT fGsp gspParams [.op .sub [vv gF, .const 1], vv gA] (gspBody C)
        [BitVec.ofNat 64 f, Enc.idxW fn] (by decide) rfl (by decide) hcs
        ⟨by simp +decide [sev, Env.get, gspParams, ctxEnv]
            rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; rfl,
          by simp, trivial⟩
        (fun r w s' st => getAppSpineGo f fn s = .ok (r, s') ∧ PostSp (ctxH C H) s r w s' st)
        (fun r w s' H' => s' = s ∧ ∃ o pa pn, w = cellA C o ∧ H'[o]? = some (Enc.idxW r.1) ∧
          H'[o + 1]? = some (cellA C pa) ∧ H'[o + 2]? = some (cellA C pn) ∧
          BlkAt H' pa (r.2.1.toList.map Enc.idxW) ∧ BlkAt H' pn (r.2.2.toList.map Enc.idxW))
        (fun r w s' st ⟨_, hs, H', o, pa, pn, hp, hw, h0, h1, h2, hba, hbn, hsr⟩ =>
          ⟨H', hp, ⟨hs, o, pa, pn, hw, h0, h1, h2, hba, hbn⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu gspParams _ rfl hlk)
          (ih (by omega) H s fn hpre)))
        (fun r w s1 H1 hp1 ⟨hs, o, pa, pn, hw, h0, h1, h2, hba, hbn⟩ => ?_)
      subst hs hw
      refine UD.specR_heapLoadI' (C := ctxH C H1) gHd (vv gT) o _ h0 (by decide) (by simp; rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) gPa _ (o + 1) _ h1 (by decide)
        (by simp [sev]; exact cellA_add8 C o) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) gPn _ (o + 2) _ h2 (by decide)
        (by simp [sev]; rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl]; exact ExPre.cellA_off C _ 2) ?_
      refine specR_callApp (C := ctxH C H1) (ctxOK_H hok _) hca gPa2 (vv gPa) (vv gB) pa _ (Enc.idxW a) (by decide)
        hba (by simp; rfl) (by simp) (fun H2 o2 hp2 hb2 => ?_)
      refine specR_callApp (C := ctxH C H2) (ctxOK_H hok _) hca gPn2 (vv gPn) (vv gH) pn _ (Enc.idxW h) (by decide)
        (blkAt_mono hbn hp2) (by simp; rfl) (by simp +decide [Env.get, gspParams, ctxEnv]) (fun H3 o3 hp3 hb3 => ?_)
      refine specR_tripRet (C0 := ctxH C H) (H := H3) (r := (r.1, r.2.1.push a, r.2.2.push h)) hok' gR gHd gPa2
        gPn2 o2 o3 (by decide) (by decide) (by simp) (by simp; rfl) (by simp; rfl)
        (hp1.trans (hp2.trans hp3)) (by simpa using blkAt_mono hb2 hp3) (by simpa using hb3)
    · rw [ite_eq_right (show ¬ (h.tag == ETag.app) = true from ht)]
      refine specR_ifI _ 0 (by rw [hT]; simp [ht, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_emptyBlk (C0 := C) (H := H) hok gE1 (by decide) (fun H1 o1 hp1 hb1 => ?_)
      refine specR_emptyBlk (C0 := C) (H := H1) hok gE2 (by decide) (fun H2 o2 hp2 hb2 => ?_)
      exact specR_tripRet (C0 := ctxH C H) (H := H2) (r := (h, #[], #[])) hok' gR gH gE1 gE2 o1 o2 (by decide)
        (by decide) (by simp +decide [Env.get, gspParams, ctxEnv]) (by simp; rfl) (by simp; rfl) (hp1.trans hp2)
        (by simpa using blkAt_mono hb1 hp2) (by simpa using hb2)

end

end ConPanqueque.T.WC
