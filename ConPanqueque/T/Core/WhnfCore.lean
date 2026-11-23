import ConPanqueque.T.Core.WcTags
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfCoreLoop` as a recursive function

One call is one iteration of the twin's loop: the easy case, the memo lookup, then one `whnfCoreStep` (a
function, given by its spec), the pending keys pushed, and either the chain stored and the answer returned, or
the next iteration called.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot

theorem whnfCoreLoop_succ (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (d n : Nat) (e : EIdx)
    (pend pendC : Array EIdx) :
    whnfCoreLoop mode r fe cheap d (n + 1) e pend pendC =
      (if whnfCoreStuckTag e then (whnfCoreStoreChain cheap pend pendC e >>= fun _ => pure e) else
        (getAppFn coreWalkFuel e >>= fun h =>
          whnfCoreLookupAt (whnfCoreKey h e) cheap e >>= fun o => match o with
          | some x => whnfCoreStoreChain cheap pend #[] x >>= fun _ => pure x
          | none => whnfCoreStep mode r fe cheap d h e >>= fun st => match st with
            | .done v =>
              (if cheap then pure false else pure (whnfCoreStoresDone (whnfCoreKey h e) e v) : AM Bool) >>= fun stb =>
              whnfCoreStoreChain cheap (pushKey stb e pend) (pushCheapKey (whnfCoreCheapSafe h e) stb e pendC) v >>=
                fun _ => pure v
            | .cont e' =>
              (if cheap then pure false else pure (whnfCoreKey h e) : AM Bool) >>= fun stb =>
              whnfCoreLoop mode r fe cheap d n e' (pushKey stb e pend) (pushCheapKey (whnfCoreCheapSafe h e) stb e pendC))) := by
  rfl


def cH := ofString "wch"
def cK := ofString "wck"
def cX := ofString "wcx"
def cS := ofString "wcs"
def cT := ofString "wct"
def cND := ofString "wcn1"
def cND2 := ofString "wcn2"
def cStb := ofString "wcb"
def cB := ofString "wcbud"
def sH := ofString "wsh"
def sE := ofString "wse"
def fWCL := ofString "whnfCoreLoop"
def fWCS := ofString "whnfCoreStep"

@[simp] theorem wcl_cH_ne_cK : cH ≠ cK := by decide
@[simp] theorem wcl_cH_ne_cX : cH ≠ cX := by decide
@[simp] theorem wcl_cH_ne_cS : cH ≠ cS := by decide
@[simp] theorem wcl_cH_ne_cT : cH ≠ cT := by decide
@[simp] theorem wcl_cH_ne_cND : cH ≠ cND := by decide
@[simp] theorem wcl_cH_ne_cND2 : cH ≠ cND2 := by decide
@[simp] theorem wcl_cH_ne_cStb : cH ≠ cStb := by decide
@[simp] theorem wcl_cH_ne_cB : cH ≠ cB := by decide
@[simp] theorem wcl_cH_ne_sH : cH ≠ sH := by decide
@[simp] theorem wcl_cH_ne_sE : cH ≠ sE := by decide
@[simp] theorem wcl_cH_ne_kC : cH ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cH : kC ≠ cH := by decide
@[simp] theorem wcl_cH_ne_kFu : cH ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cH : kFu ≠ cH := by decide
@[simp] theorem wcl_cH_ne_kD : cH ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cH : kD ≠ cH := by decide
@[simp] theorem wcl_cH_ne_kE : cH ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cH : kE ≠ cH := by decide
@[simp] theorem wcl_cH_ne_lEo : cH ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cH : lEo ≠ cH := by decide
@[simp] theorem wcl_cH_ne_lKb : cH ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cH : lKb ≠ cH := by decide
@[simp] theorem wcl_cH_ne_cP : cH ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cH : cP ≠ cH := by decide
@[simp] theorem wcl_cH_ne_cQ : cH ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cH : cQ ≠ cH := by decide
@[simp] theorem wcl_cH_ne_cV : cH ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cH : cV ≠ cH := by decide
@[simp] theorem wcl_cH_ne_cR : cH ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cH : cR ≠ cH := by decide
@[simp] theorem wcl_cH_ne_lFle : cH ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cH : lFle ≠ cH := by decide
@[simp] theorem wcl_cH_ne_lDir : cH ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cH : lDir ≠ cH := by decide
@[simp] theorem wcl_cH_ne_pFu : cH ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cH : pFu ≠ cH := by decide
@[simp] theorem wcl_cH_ne_pH : cH ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cH : pH ≠ cH := by decide
@[simp] theorem wcl_cK_ne_cH : cK ≠ cH := by decide
@[simp] theorem wcl_cK_ne_cX : cK ≠ cX := by decide
@[simp] theorem wcl_cK_ne_cS : cK ≠ cS := by decide
@[simp] theorem wcl_cK_ne_cT : cK ≠ cT := by decide
@[simp] theorem wcl_cK_ne_cND : cK ≠ cND := by decide
@[simp] theorem wcl_cK_ne_cND2 : cK ≠ cND2 := by decide
@[simp] theorem wcl_cK_ne_cStb : cK ≠ cStb := by decide
@[simp] theorem wcl_cK_ne_cB : cK ≠ cB := by decide
@[simp] theorem wcl_cK_ne_sH : cK ≠ sH := by decide
@[simp] theorem wcl_cK_ne_sE : cK ≠ sE := by decide
@[simp] theorem wcl_cK_ne_kC : cK ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cK : kC ≠ cK := by decide
@[simp] theorem wcl_cK_ne_kFu : cK ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cK : kFu ≠ cK := by decide
@[simp] theorem wcl_cK_ne_kD : cK ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cK : kD ≠ cK := by decide
@[simp] theorem wcl_cK_ne_kE : cK ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cK : kE ≠ cK := by decide
@[simp] theorem wcl_cK_ne_lEo : cK ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cK : lEo ≠ cK := by decide
@[simp] theorem wcl_cK_ne_lKb : cK ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cK : lKb ≠ cK := by decide
@[simp] theorem wcl_cK_ne_cP : cK ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cK : cP ≠ cK := by decide
@[simp] theorem wcl_cK_ne_cQ : cK ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cK : cQ ≠ cK := by decide
@[simp] theorem wcl_cK_ne_cV : cK ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cK : cV ≠ cK := by decide
@[simp] theorem wcl_cK_ne_cR : cK ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cK : cR ≠ cK := by decide
@[simp] theorem wcl_cK_ne_lFle : cK ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cK : lFle ≠ cK := by decide
@[simp] theorem wcl_cK_ne_lDir : cK ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cK : lDir ≠ cK := by decide
@[simp] theorem wcl_cK_ne_pFu : cK ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cK : pFu ≠ cK := by decide
@[simp] theorem wcl_cK_ne_pH : cK ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cK : pH ≠ cK := by decide
@[simp] theorem wcl_cX_ne_cH : cX ≠ cH := by decide
@[simp] theorem wcl_cX_ne_cK : cX ≠ cK := by decide
@[simp] theorem wcl_cX_ne_cS : cX ≠ cS := by decide
@[simp] theorem wcl_cX_ne_cT : cX ≠ cT := by decide
@[simp] theorem wcl_cX_ne_cND : cX ≠ cND := by decide
@[simp] theorem wcl_cX_ne_cND2 : cX ≠ cND2 := by decide
@[simp] theorem wcl_cX_ne_cStb : cX ≠ cStb := by decide
@[simp] theorem wcl_cX_ne_cB : cX ≠ cB := by decide
@[simp] theorem wcl_cX_ne_sH : cX ≠ sH := by decide
@[simp] theorem wcl_cX_ne_sE : cX ≠ sE := by decide
@[simp] theorem wcl_cX_ne_kC : cX ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cX : kC ≠ cX := by decide
@[simp] theorem wcl_cX_ne_kFu : cX ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cX : kFu ≠ cX := by decide
@[simp] theorem wcl_cX_ne_kD : cX ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cX : kD ≠ cX := by decide
@[simp] theorem wcl_cX_ne_kE : cX ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cX : kE ≠ cX := by decide
@[simp] theorem wcl_cX_ne_lEo : cX ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cX : lEo ≠ cX := by decide
@[simp] theorem wcl_cX_ne_lKb : cX ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cX : lKb ≠ cX := by decide
@[simp] theorem wcl_cX_ne_cP : cX ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cX : cP ≠ cX := by decide
@[simp] theorem wcl_cX_ne_cQ : cX ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cX : cQ ≠ cX := by decide
@[simp] theorem wcl_cX_ne_cV : cX ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cX : cV ≠ cX := by decide
@[simp] theorem wcl_cX_ne_cR : cX ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cX : cR ≠ cX := by decide
@[simp] theorem wcl_cX_ne_lFle : cX ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cX : lFle ≠ cX := by decide
@[simp] theorem wcl_cX_ne_lDir : cX ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cX : lDir ≠ cX := by decide
@[simp] theorem wcl_cX_ne_pFu : cX ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cX : pFu ≠ cX := by decide
@[simp] theorem wcl_cX_ne_pH : cX ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cX : pH ≠ cX := by decide
@[simp] theorem wcl_cS_ne_cH : cS ≠ cH := by decide
@[simp] theorem wcl_cS_ne_cK : cS ≠ cK := by decide
@[simp] theorem wcl_cS_ne_cX : cS ≠ cX := by decide
@[simp] theorem wcl_cS_ne_cT : cS ≠ cT := by decide
@[simp] theorem wcl_cS_ne_cND : cS ≠ cND := by decide
@[simp] theorem wcl_cS_ne_cND2 : cS ≠ cND2 := by decide
@[simp] theorem wcl_cS_ne_cStb : cS ≠ cStb := by decide
@[simp] theorem wcl_cS_ne_cB : cS ≠ cB := by decide
@[simp] theorem wcl_cS_ne_sH : cS ≠ sH := by decide
@[simp] theorem wcl_cS_ne_sE : cS ≠ sE := by decide
@[simp] theorem wcl_cS_ne_kC : cS ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cS : kC ≠ cS := by decide
@[simp] theorem wcl_cS_ne_kFu : cS ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cS : kFu ≠ cS := by decide
@[simp] theorem wcl_cS_ne_kD : cS ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cS : kD ≠ cS := by decide
@[simp] theorem wcl_cS_ne_kE : cS ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cS : kE ≠ cS := by decide
@[simp] theorem wcl_cS_ne_lEo : cS ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cS : lEo ≠ cS := by decide
@[simp] theorem wcl_cS_ne_lKb : cS ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cS : lKb ≠ cS := by decide
@[simp] theorem wcl_cS_ne_cP : cS ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cS : cP ≠ cS := by decide
@[simp] theorem wcl_cS_ne_cQ : cS ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cS : cQ ≠ cS := by decide
@[simp] theorem wcl_cS_ne_cV : cS ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cS : cV ≠ cS := by decide
@[simp] theorem wcl_cS_ne_cR : cS ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cS : cR ≠ cS := by decide
@[simp] theorem wcl_cS_ne_lFle : cS ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cS : lFle ≠ cS := by decide
@[simp] theorem wcl_cS_ne_lDir : cS ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cS : lDir ≠ cS := by decide
@[simp] theorem wcl_cS_ne_pFu : cS ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cS : pFu ≠ cS := by decide
@[simp] theorem wcl_cS_ne_pH : cS ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cS : pH ≠ cS := by decide
@[simp] theorem wcl_cT_ne_cH : cT ≠ cH := by decide
@[simp] theorem wcl_cT_ne_cK : cT ≠ cK := by decide
@[simp] theorem wcl_cT_ne_cX : cT ≠ cX := by decide
@[simp] theorem wcl_cT_ne_cS : cT ≠ cS := by decide
@[simp] theorem wcl_cT_ne_cND : cT ≠ cND := by decide
@[simp] theorem wcl_cT_ne_cND2 : cT ≠ cND2 := by decide
@[simp] theorem wcl_cT_ne_cStb : cT ≠ cStb := by decide
@[simp] theorem wcl_cT_ne_cB : cT ≠ cB := by decide
@[simp] theorem wcl_cT_ne_sH : cT ≠ sH := by decide
@[simp] theorem wcl_cT_ne_sE : cT ≠ sE := by decide
@[simp] theorem wcl_cT_ne_kC : cT ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cT : kC ≠ cT := by decide
@[simp] theorem wcl_cT_ne_kFu : cT ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cT : kFu ≠ cT := by decide
@[simp] theorem wcl_cT_ne_kD : cT ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cT : kD ≠ cT := by decide
@[simp] theorem wcl_cT_ne_kE : cT ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cT : kE ≠ cT := by decide
@[simp] theorem wcl_cT_ne_lEo : cT ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cT : lEo ≠ cT := by decide
@[simp] theorem wcl_cT_ne_lKb : cT ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cT : lKb ≠ cT := by decide
@[simp] theorem wcl_cT_ne_cP : cT ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cT : cP ≠ cT := by decide
@[simp] theorem wcl_cT_ne_cQ : cT ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cT : cQ ≠ cT := by decide
@[simp] theorem wcl_cT_ne_cV : cT ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cT : cV ≠ cT := by decide
@[simp] theorem wcl_cT_ne_cR : cT ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cT : cR ≠ cT := by decide
@[simp] theorem wcl_cT_ne_lFle : cT ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cT : lFle ≠ cT := by decide
@[simp] theorem wcl_cT_ne_lDir : cT ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cT : lDir ≠ cT := by decide
@[simp] theorem wcl_cT_ne_pFu : cT ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cT : pFu ≠ cT := by decide
@[simp] theorem wcl_cT_ne_pH : cT ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cT : pH ≠ cT := by decide
@[simp] theorem wcl_cND_ne_cH : cND ≠ cH := by decide
@[simp] theorem wcl_cND_ne_cK : cND ≠ cK := by decide
@[simp] theorem wcl_cND_ne_cX : cND ≠ cX := by decide
@[simp] theorem wcl_cND_ne_cS : cND ≠ cS := by decide
@[simp] theorem wcl_cND_ne_cT : cND ≠ cT := by decide
@[simp] theorem wcl_cND_ne_cND2 : cND ≠ cND2 := by decide
@[simp] theorem wcl_cND_ne_cStb : cND ≠ cStb := by decide
@[simp] theorem wcl_cND_ne_cB : cND ≠ cB := by decide
@[simp] theorem wcl_cND_ne_sH : cND ≠ sH := by decide
@[simp] theorem wcl_cND_ne_sE : cND ≠ sE := by decide
@[simp] theorem wcl_cND_ne_kC : cND ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cND : kC ≠ cND := by decide
@[simp] theorem wcl_cND_ne_kFu : cND ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cND : kFu ≠ cND := by decide
@[simp] theorem wcl_cND_ne_kD : cND ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cND : kD ≠ cND := by decide
@[simp] theorem wcl_cND_ne_kE : cND ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cND : kE ≠ cND := by decide
@[simp] theorem wcl_cND_ne_lEo : cND ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cND : lEo ≠ cND := by decide
@[simp] theorem wcl_cND_ne_lKb : cND ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cND : lKb ≠ cND := by decide
@[simp] theorem wcl_cND_ne_cP : cND ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cND : cP ≠ cND := by decide
@[simp] theorem wcl_cND_ne_cQ : cND ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cND : cQ ≠ cND := by decide
@[simp] theorem wcl_cND_ne_cV : cND ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cND : cV ≠ cND := by decide
@[simp] theorem wcl_cND_ne_cR : cND ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cND : cR ≠ cND := by decide
@[simp] theorem wcl_cND_ne_lFle : cND ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cND : lFle ≠ cND := by decide
@[simp] theorem wcl_cND_ne_lDir : cND ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cND : lDir ≠ cND := by decide
@[simp] theorem wcl_cND_ne_pFu : cND ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cND : pFu ≠ cND := by decide
@[simp] theorem wcl_cND_ne_pH : cND ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cND : pH ≠ cND := by decide
@[simp] theorem wcl_cND2_ne_cH : cND2 ≠ cH := by decide
@[simp] theorem wcl_cND2_ne_cK : cND2 ≠ cK := by decide
@[simp] theorem wcl_cND2_ne_cX : cND2 ≠ cX := by decide
@[simp] theorem wcl_cND2_ne_cS : cND2 ≠ cS := by decide
@[simp] theorem wcl_cND2_ne_cT : cND2 ≠ cT := by decide
@[simp] theorem wcl_cND2_ne_cND : cND2 ≠ cND := by decide
@[simp] theorem wcl_cND2_ne_cStb : cND2 ≠ cStb := by decide
@[simp] theorem wcl_cND2_ne_cB : cND2 ≠ cB := by decide
@[simp] theorem wcl_cND2_ne_sH : cND2 ≠ sH := by decide
@[simp] theorem wcl_cND2_ne_sE : cND2 ≠ sE := by decide
@[simp] theorem wcl_cND2_ne_kC : cND2 ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cND2 : kC ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_kFu : cND2 ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cND2 : kFu ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_kD : cND2 ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cND2 : kD ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_kE : cND2 ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cND2 : kE ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_lEo : cND2 ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cND2 : lEo ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_lKb : cND2 ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cND2 : lKb ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_cP : cND2 ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cND2 : cP ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_cQ : cND2 ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cND2 : cQ ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_cV : cND2 ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cND2 : cV ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_cR : cND2 ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cND2 : cR ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_lFle : cND2 ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cND2 : lFle ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_lDir : cND2 ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cND2 : lDir ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_pFu : cND2 ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cND2 : pFu ≠ cND2 := by decide
@[simp] theorem wcl_cND2_ne_pH : cND2 ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cND2 : pH ≠ cND2 := by decide
@[simp] theorem wcl_cStb_ne_cH : cStb ≠ cH := by decide
@[simp] theorem wcl_cStb_ne_cK : cStb ≠ cK := by decide
@[simp] theorem wcl_cStb_ne_cX : cStb ≠ cX := by decide
@[simp] theorem wcl_cStb_ne_cS : cStb ≠ cS := by decide
@[simp] theorem wcl_cStb_ne_cT : cStb ≠ cT := by decide
@[simp] theorem wcl_cStb_ne_cND : cStb ≠ cND := by decide
@[simp] theorem wcl_cStb_ne_cND2 : cStb ≠ cND2 := by decide
@[simp] theorem wcl_cStb_ne_cB : cStb ≠ cB := by decide
@[simp] theorem wcl_cStb_ne_sH : cStb ≠ sH := by decide
@[simp] theorem wcl_cStb_ne_sE : cStb ≠ sE := by decide
@[simp] theorem wcl_cStb_ne_kC : cStb ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cStb : kC ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_kFu : cStb ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cStb : kFu ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_kD : cStb ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cStb : kD ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_kE : cStb ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cStb : kE ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_lEo : cStb ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cStb : lEo ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_lKb : cStb ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cStb : lKb ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_cP : cStb ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cStb : cP ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_cQ : cStb ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cStb : cQ ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_cV : cStb ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cStb : cV ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_cR : cStb ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cStb : cR ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_lFle : cStb ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cStb : lFle ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_lDir : cStb ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cStb : lDir ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_pFu : cStb ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cStb : pFu ≠ cStb := by decide
@[simp] theorem wcl_cStb_ne_pH : cStb ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cStb : pH ≠ cStb := by decide
@[simp] theorem wcl_cB_ne_cH : cB ≠ cH := by decide
@[simp] theorem wcl_cB_ne_cK : cB ≠ cK := by decide
@[simp] theorem wcl_cB_ne_cX : cB ≠ cX := by decide
@[simp] theorem wcl_cB_ne_cS : cB ≠ cS := by decide
@[simp] theorem wcl_cB_ne_cT : cB ≠ cT := by decide
@[simp] theorem wcl_cB_ne_cND : cB ≠ cND := by decide
@[simp] theorem wcl_cB_ne_cND2 : cB ≠ cND2 := by decide
@[simp] theorem wcl_cB_ne_cStb : cB ≠ cStb := by decide
@[simp] theorem wcl_cB_ne_sH : cB ≠ sH := by decide
@[simp] theorem wcl_cB_ne_sE : cB ≠ sE := by decide
@[simp] theorem wcl_cB_ne_kC : cB ≠ kC := by decide
@[simp] theorem wcl_kC_ne_cB : kC ≠ cB := by decide
@[simp] theorem wcl_cB_ne_kFu : cB ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_cB : kFu ≠ cB := by decide
@[simp] theorem wcl_cB_ne_kD : cB ≠ kD := by decide
@[simp] theorem wcl_kD_ne_cB : kD ≠ cB := by decide
@[simp] theorem wcl_cB_ne_kE : cB ≠ kE := by decide
@[simp] theorem wcl_kE_ne_cB : kE ≠ cB := by decide
@[simp] theorem wcl_cB_ne_lEo : cB ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_cB : lEo ≠ cB := by decide
@[simp] theorem wcl_cB_ne_lKb : cB ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_cB : lKb ≠ cB := by decide
@[simp] theorem wcl_cB_ne_cP : cB ≠ cP := by decide
@[simp] theorem wcl_cP_ne_cB : cP ≠ cB := by decide
@[simp] theorem wcl_cB_ne_cQ : cB ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_cB : cQ ≠ cB := by decide
@[simp] theorem wcl_cB_ne_cV : cB ≠ cV := by decide
@[simp] theorem wcl_cV_ne_cB : cV ≠ cB := by decide
@[simp] theorem wcl_cB_ne_cR : cB ≠ cR := by decide
@[simp] theorem wcl_cR_ne_cB : cR ≠ cB := by decide
@[simp] theorem wcl_cB_ne_lFle : cB ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_cB : lFle ≠ cB := by decide
@[simp] theorem wcl_cB_ne_lDir : cB ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_cB : lDir ≠ cB := by decide
@[simp] theorem wcl_cB_ne_pFu : cB ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_cB : pFu ≠ cB := by decide
@[simp] theorem wcl_cB_ne_pH : cB ≠ pH := by decide
@[simp] theorem wcl_pH_ne_cB : pH ≠ cB := by decide
@[simp] theorem wcl_sH_ne_cH : sH ≠ cH := by decide
@[simp] theorem wcl_sH_ne_cK : sH ≠ cK := by decide
@[simp] theorem wcl_sH_ne_cX : sH ≠ cX := by decide
@[simp] theorem wcl_sH_ne_cS : sH ≠ cS := by decide
@[simp] theorem wcl_sH_ne_cT : sH ≠ cT := by decide
@[simp] theorem wcl_sH_ne_cND : sH ≠ cND := by decide
@[simp] theorem wcl_sH_ne_cND2 : sH ≠ cND2 := by decide
@[simp] theorem wcl_sH_ne_cStb : sH ≠ cStb := by decide
@[simp] theorem wcl_sH_ne_cB : sH ≠ cB := by decide
@[simp] theorem wcl_sH_ne_sE : sH ≠ sE := by decide
@[simp] theorem wcl_sH_ne_kC : sH ≠ kC := by decide
@[simp] theorem wcl_kC_ne_sH : kC ≠ sH := by decide
@[simp] theorem wcl_sH_ne_kFu : sH ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_sH : kFu ≠ sH := by decide
@[simp] theorem wcl_sH_ne_kD : sH ≠ kD := by decide
@[simp] theorem wcl_kD_ne_sH : kD ≠ sH := by decide
@[simp] theorem wcl_sH_ne_kE : sH ≠ kE := by decide
@[simp] theorem wcl_kE_ne_sH : kE ≠ sH := by decide
@[simp] theorem wcl_sH_ne_lEo : sH ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_sH : lEo ≠ sH := by decide
@[simp] theorem wcl_sH_ne_lKb : sH ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_sH : lKb ≠ sH := by decide
@[simp] theorem wcl_sH_ne_cP : sH ≠ cP := by decide
@[simp] theorem wcl_cP_ne_sH : cP ≠ sH := by decide
@[simp] theorem wcl_sH_ne_cQ : sH ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_sH : cQ ≠ sH := by decide
@[simp] theorem wcl_sH_ne_cV : sH ≠ cV := by decide
@[simp] theorem wcl_cV_ne_sH : cV ≠ sH := by decide
@[simp] theorem wcl_sH_ne_cR : sH ≠ cR := by decide
@[simp] theorem wcl_cR_ne_sH : cR ≠ sH := by decide
@[simp] theorem wcl_sH_ne_lFle : sH ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_sH : lFle ≠ sH := by decide
@[simp] theorem wcl_sH_ne_lDir : sH ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_sH : lDir ≠ sH := by decide
@[simp] theorem wcl_sH_ne_pFu : sH ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_sH : pFu ≠ sH := by decide
@[simp] theorem wcl_sH_ne_pH : sH ≠ pH := by decide
@[simp] theorem wcl_pH_ne_sH : pH ≠ sH := by decide
@[simp] theorem wcl_sE_ne_cH : sE ≠ cH := by decide
@[simp] theorem wcl_sE_ne_cK : sE ≠ cK := by decide
@[simp] theorem wcl_sE_ne_cX : sE ≠ cX := by decide
@[simp] theorem wcl_sE_ne_cS : sE ≠ cS := by decide
@[simp] theorem wcl_sE_ne_cT : sE ≠ cT := by decide
@[simp] theorem wcl_sE_ne_cND : sE ≠ cND := by decide
@[simp] theorem wcl_sE_ne_cND2 : sE ≠ cND2 := by decide
@[simp] theorem wcl_sE_ne_cStb : sE ≠ cStb := by decide
@[simp] theorem wcl_sE_ne_cB : sE ≠ cB := by decide
@[simp] theorem wcl_sE_ne_sH : sE ≠ sH := by decide
@[simp] theorem wcl_sE_ne_kC : sE ≠ kC := by decide
@[simp] theorem wcl_kC_ne_sE : kC ≠ sE := by decide
@[simp] theorem wcl_sE_ne_kFu : sE ≠ kFu := by decide
@[simp] theorem wcl_kFu_ne_sE : kFu ≠ sE := by decide
@[simp] theorem wcl_sE_ne_kD : sE ≠ kD := by decide
@[simp] theorem wcl_kD_ne_sE : kD ≠ sE := by decide
@[simp] theorem wcl_sE_ne_kE : sE ≠ kE := by decide
@[simp] theorem wcl_kE_ne_sE : kE ≠ sE := by decide
@[simp] theorem wcl_sE_ne_lEo : sE ≠ lEo := by decide
@[simp] theorem wcl_lEo_ne_sE : lEo ≠ sE := by decide
@[simp] theorem wcl_sE_ne_lKb : sE ≠ lKb := by decide
@[simp] theorem wcl_lKb_ne_sE : lKb ≠ sE := by decide
@[simp] theorem wcl_sE_ne_cP : sE ≠ cP := by decide
@[simp] theorem wcl_cP_ne_sE : cP ≠ sE := by decide
@[simp] theorem wcl_sE_ne_cQ : sE ≠ cQ := by decide
@[simp] theorem wcl_cQ_ne_sE : cQ ≠ sE := by decide
@[simp] theorem wcl_sE_ne_cV : sE ≠ cV := by decide
@[simp] theorem wcl_cV_ne_sE : cV ≠ sE := by decide
@[simp] theorem wcl_sE_ne_cR : sE ≠ cR := by decide
@[simp] theorem wcl_cR_ne_sE : cR ≠ sE := by decide
@[simp] theorem wcl_sE_ne_lFle : sE ≠ lFle := by decide
@[simp] theorem wcl_lFle_ne_sE : lFle ≠ sE := by decide
@[simp] theorem wcl_sE_ne_lDir : sE ≠ lDir := by decide
@[simp] theorem wcl_lDir_ne_sE : lDir ≠ sE := by decide
@[simp] theorem wcl_sE_ne_pFu : sE ≠ pFu := by decide
@[simp] theorem wcl_pFu_ne_sE : pFu ≠ sE := by decide
@[simp] theorem wcl_sE_ne_pH : sE ≠ pH := by decide
@[simp] theorem wcl_pH_ne_sE : pH ≠ sE := by decide

/-- A `WhnfStep` as a word: the handle shifted up, the low bit set for `cont`. -/
def encWS : WhnfStep → BitVec 64
  | .done v => Enc.idxW v <<< 1
  | .cont e => (Enc.idxW e <<< 1) + 1

def wcsParams : List MlS := [kFu, kC, kD, sH, sE]
def wclParams : List MlS := [kFu, kC, kD, kE, cP, cQ, cB]
def wclLocals : List MlS := [cV, cR, cH, cK, cX, cS, cT, cND, cND2, cStb, lEo]

def wclRest (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .notEqual (vv cX) (.const 0))
    (.seq (.assign .local cQ (.const 0)) (.seq (.assign .local cV (.op .sub [vv cX, .const 1])) scRet))
  (.seq (.assign .local cS (safeE cH kE))
  (.seq (.call (some (some (.local, cT), none)) fWCS [vv kFu, vv kC, vv kD, vv cH, vv kE])
  (.seq (.assign .local cV (.shift .lsr (vv cT) (.const 1)))
  (.ite (.op .and [vv cT, .const 1])
    (.seq (.assign .local cStb (andE (notE (vv kC)) (vv cK)))
      (pushP C cP cND cStb kE (pushP C cQ cND2 cStb kE
      (.seq (.assign .local cQ (.panop .mul [vv cQ, vv cS]))
      (.seq (.call (some (some (.local, cR), none)) fWCL [vv kFu, vv kC, vv kD, vv cV, vv cP, vv cQ, vv cB])
        (.return (vv cR)))))))
    (.seq (.assign .local cStb (andE (notE (vv kC)) (storesDoneE cK kE cV)))
      (pushP C cP cND cStb kE (pushP C cQ cND2 cStb kE
      (.seq (.assign .local cQ (.panop .mul [vv cQ, vv cS])) scRet))))))))

def wclCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv cB) (.const 0)) hang
  (.seq (.assign .local cB (.op .sub [vv cB, .const 1]))
  (.ite (stuckTagE kE) (.seq (.assign .local cV (vv kE)) scRet)
  (.seq (.call (some (some (.local, cH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv kE])
  (.seq (.assign .local cK (keyE cH kE))
  (.ite (vv cK)
    (.ite (vv kC) (modeGetP C CacheK.whnfCoreCheap cX (vv kE) (wclRest C))
      (modeGetP C CacheK.whnfCore cX (vv kE) (wclRest C)))
    (.seq (.assign .local cX (.const 0)) (wclRest C)))))))

def wclBody (C : Ctx) : ProgHOL 64 := prologue wclLocals (wclCore C)


section
variable {σ : Type}

def PostWS (C : Ctx) (st : WhnfStep) (w : BitVec 64) (s' : AState) (t : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = encWS st ∧ SR (ctxH C H') s' t

theorem idxW_lt (h : EIdx) : (Enc.idxW h).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact h.word.toNat_lt

theorem encWS_shr (st : WhnfStep) : encWS st >>> 1 = Enc.idxW (match st with | .done v => v | .cont e => e) := by
  apply BitVec.eq_of_toNat_eq
  cases st with
  | done v =>
    have := idxW_lt v
    simp [encWS, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  | cont e =>
    have := idxW_lt e
    simp [encWS, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega

theorem encWS_and1 (st : WhnfStep) : encWS st &&& 1#64 = boolW (match st with | .done _ => false | .cont _ => true) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
  cases st with
  | done v =>
    have := idxW_lt v
    simp only [encWS, BitVec.toNat_and, e1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp [boolW]; omega
  | cont e =>
    have := idxW_lt e
    simp only [encWS, BitVec.toNat_and, e1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq]
    simp [boolW]; omega

theorem pushKey_rev (b : Bool) (e : EIdx) (xs : List EIdx) :
    pushKey b e xs.reverse.toArray = (if b then e :: xs else xs).reverse.toArray := by
  cases b <;> simp [pushKey]

theorem pushCheapKey_rev (safe b : Bool) (e : EIdx) (ys : List EIdx) :
    pushCheapKey safe b e ys.reverse.toArray =
      (if safe then (if b then e :: ys else ys) else []).reverse.toArray := by
  cases safe <;> cases b <;> simp [pushCheapKey, pushKey]

end


section
variable {σ : Type}

/-- A local the environment binds may be declared. -/
theorem specR_declAdd {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (v : BitVec 64) (hx : Γ.get x = some v)
    (h : SpecR (Inv C s Γ M (x :: D)) c s m R) : SpecR (Inv C s Γ M D) c s m R :=
  fun t ht => h t ⟨ht.sr, ht.env, ht.mem, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨v, ht.env y v hx⟩
    · exact ht.decl y hy⟩

abbrev wclD : List MlS := cB :: cQ :: cP :: (ctxLocals ++ wclLocals)

theorem wcl_rest (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (hok : CtxOK C) (Bs : ProgHOL 64)
    (hcf : C.code.lookup fSCF = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody .whnfCore C fSCF, .one))
    (hcc : C.code.lookup fSCC = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody .whnfCoreCheap C fSCC, .one))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (hcs : C.code.lookup fWCS = some (wcsParams.map (fun p => (p, ShapeHOL.one)), Bs, .one))
    (hcl : C.code.lookup fWCL = some (wclParams.map (fun p => (p, ShapeHOL.one)), wclBody C, .one))
    (Q : AState → Prop)
    (hQs : ∀ s1 cheap d h e a s2, Q s1 → whnfCoreStep mode (knot mode C n) C.fe cheap d h e s1 = .ok (a, s2) → Q s2)
    (hStep : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ cheap d h e,
      SpecR (σ := σ) (Pre (ctxH C H) s1 (wcsParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d,
        Enc.idxW h, Enc.idxW e])) Bs s1 (whnfCoreStep mode (knot mode C n) C.fe cheap d h e) (PostWS (ctxH C H)))
    (f' : Nat)
    (hrec : ∀ (H : List (BitVec 64)) s1 cheap d e (xs ys : List EIdx) p q, C.H <+: H → Q s1 → LstAt C H p xs →
      LstAt C H q ys → SpecR (σ := σ) (Pre (ctxH C H) s1 (wclParams.zip [BitVec.ofNat 64 n, boolW cheap,
        BitVec.ofNat 64 d, Enc.idxW e, p, q, BitVec.ofNat 64 f'])) (wclBody C) s1
        (whnfCoreLoop mode (knot mode C n) C.fe cheap d f' e xs.reverse.toArray ys.reverse.toArray) (PostK (ctxH C H)))
    {H : List (BitVec 64)} {s : AState} {Γ : Env} (hpre : C.H <+: H) (hq : Q s)
    (cheap : Bool) (d : Nat) (e h : EIdx) (xs ys : List EIdx) (p q : BitVec 64) (o : Option EIdx)
    (hp : LstAt C H p xs) (hqL : LstAt C H q ys)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hC : Γ.get kC = some (boolW cheap))
    (hD0 : Γ.get kD = some (BitVec.ofNat 64 d)) (hE : Γ.get kE = some (Enc.idxW e))
    (hP : Γ.get cP = some p) (hQ : Γ.get cQ = some q) (hB : Γ.get cB = some (BitVec.ofNat 64 f'))
    (hH : Γ.get cH = some (Enc.idxW h)) (hK : Γ.get cK = some (boolW (whnfCoreKey h e)))
    (hX : Γ.get cX = some (optW o)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ [] wclD) (wclRest C) s
      (match o with
        | some x => whnfCoreStoreChain cheap xs.reverse.toArray #[] x >>= fun _ => pure x
        | none => whnfCoreStep mode (knot mode C n) C.fe cheap d h e >>= fun st => match st with
          | .done v =>
            (if cheap then pure false else pure (whnfCoreStoresDone (whnfCoreKey h e) e v) : AM Bool) >>= fun stb =>
            whnfCoreStoreChain cheap (pushKey stb e xs.reverse.toArray)
              (pushCheapKey (whnfCoreCheapSafe h e) stb e ys.reverse.toArray) v >>= fun _ => pure v
          | .cont e' =>
            (if cheap then pure false else pure (whnfCoreKey h e) : AM Bool) >>= fun stb =>
            whnfCoreLoop mode (knot mode C n) C.fe cheap d f' e' (pushKey stb e xs.reverse.toArray)
              (pushCheapKey (whnfCoreCheapSafe h e) stb e ys.reverse.toArray)) (PostK C) := by
  unfold wclRest
  rcases o with _ | x
  · -- a miss: one step
    refine specR_ifI _ 0 (by simp [sev, hX, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_assignI cS (safeE cH kE) (boolW (whnfCoreCheapSafe h e)) (by decide) (sev_safe _ cH kE h e hH hE) ?_
    refine specR_callNIH (C := ctxH C H) cT fWCS wcsParams [vv kFu, vv kC, vv kD, vv cH, vv kE] Bs
      [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW h, Enc.idxW e] (by decide) rfl (by decide) hcs
      ⟨by simp [hFu], by simp [hC], by simp [hD0], by simp [hH], by simp [hE], trivial⟩
      (fun st w s' t' => whnfCoreStep mode (knot mode C n) C.fe cheap d h e s = .ok (st, s') ∧
        PostWS (ctxH C H) st w s' t')
      (fun st w s' _ => w = encWS st ∧ whnfCoreStep mode (knot mode C n) C.fe cheap d h e s = .ok (st, s'))
      (fun st w s' t' ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hrun⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu wcsParams _ rfl hlk)
        (hStep H s hpre hq cheap d h e)))
      (fun st w s1 H1 hp1 ⟨hw, hrun⟩ => ?_)
    subst hw
    have hq1 := hQs s cheap d h e st s1 hq hrun
    have hpre1 : C.H <+: H1 := hpre.trans hp1
    have hp1L : LstAt C H1 p xs := lstAt_mono hp1 p xs hp
    have hq1L : LstAt C H1 q ys := lstAt_mono hp1 q ys hqL
    refine specR_assignI cV _ (Enc.idxW (match st with | .done v => v | .cont e => e)) (by decide)
      (by simp [sev]; exact encWS_shr st) ?_
    cases st with
    | done v =>
      refine specR_ifI _ 0 (by simp [sev, encWS_and1, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      have estb : (if cheap then pure false else pure (whnfCoreStoresDone (whnfCoreKey h e) e v) : AM Bool) =
          pure (!cheap && whnfCoreStoresDone (whnfCoreKey h e) e v) := by cases cheap <;> rfl
      simp only [estb, pure_bind]
      generalize hb : (!cheap && whnfCoreStoresDone (whnfCoreKey h e) e v) = b
      refine specR_assignI (D := wclD) cStb _ (boolW b) (by decide) ?_ ?_
      · rw [← hb]
        exact sev_andE (sev_notE (by simpa [vv, sev] using hC))
          (sev_storesDone _ cK kE cV _ e v (by simp [hK]) (by simp [hE]) (by simp))
      refine specR_pushI (C0 := C) (H := H1) hok cP cND cStb kE b e p xs ⟨by decide, by decide, by decide⟩ (by decide)
        (by decide) (by simp [hP]) hp1L (by simp) (by simp [hE]) hpre1 (fun H2 p2 w2 hpa hpb hl2 => ?_)
      refine specR_pushI (C0 := C) (H := H2) hok cQ cND2 cStb kE b e q ys ⟨by decide, by decide, by decide⟩
        (by decide) (by decide) (by simp [hQ]) (lstAt_mono hpb q ys hq1L) (by simp) (by simp [hE]) hpa
        (fun H3 q3 w3 hpc hpd hl3 => ?_)
      refine specR_assignI cQ _ (if whnfCoreCheapSafe h e then q3 else 0) (by decide)
        (by simp [sev]; cases whnfCoreCheapSafe h e <;> simp [boolW]) ?_
      have hl3' : LstAt C H3 (if whnfCoreCheapSafe h e then q3 else 0)
          (if whnfCoreCheapSafe h e then (if b then e :: ys else ys) else []) := by
        cases whnfCoreCheapSafe h e
        · rfl
        · exact hl3
      rw [pushKey_rev, pushCheapKey_rev]
      exact scRet_spec (σ := σ) (D := wclD) hok hcf hcc hcodeS hcodeI hpc cheap _ _ p2 _ v
        (lstAt_mono hpd p2 _ hl2) hl3' (by simp [hC]) (by simp) (by simp) (by simp) (by decide)
    | cont e' =>
      refine specR_ifI _ 1 (by simp [sev, encWS_and1, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      have estb : (if cheap then pure false else pure (whnfCoreKey h e) : AM Bool) =
          pure (!cheap && whnfCoreKey h e) := by cases cheap <;> rfl
      simp only [estb, pure_bind]
      generalize hb : (!cheap && whnfCoreKey h e) = b
      refine specR_assignI (D := wclD) cStb _ (boolW b) (by decide) ?_ ?_
      · rw [← hb]
        exact sev_andE (sev_notE (by simpa [vv, sev] using hC)) (by simpa [vv, sev] using hK)
      refine specR_pushI (C0 := C) (H := H1) hok cP cND cStb kE b e p xs ⟨by decide, by decide, by decide⟩ (by decide)
        (by decide) (by simp [hP]) hp1L (by simp) (by simp [hE]) hpre1 (fun H2 p2 w2 hpa hpb hl2 => ?_)
      refine specR_pushI (C0 := C) (H := H2) hok cQ cND2 cStb kE b e q ys ⟨by decide, by decide, by decide⟩
        (by decide) (by decide) (by simp [hQ]) (lstAt_mono hpb q ys hq1L) (by simp) (by simp [hE]) hpa
        (fun H3 q3 w3 hpc hpd hl3 => ?_)
      refine specR_assignI cQ _ (if whnfCoreCheapSafe h e then q3 else 0) (by decide)
        (by simp [sev]; cases whnfCoreCheapSafe h e <;> simp [boolW]) ?_
      have hl3' : LstAt C H3 (if whnfCoreCheapSafe h e then q3 else 0)
          (if whnfCoreCheapSafe h e then (if b then e :: ys else ys) else []) := by
        cases whnfCoreCheapSafe h e
        · rfl
        · exact hl3
      rw [pushKey_rev, pushCheapKey_rev]
      refine specR_congr (m' := whnfCoreLoop mode (knot mode C n) C.fe cheap d f' e'
        (if b then e :: xs else xs).reverse.toArray
        (if whnfCoreCheapSafe h e then (if b then e :: ys else ys) else []).reverse.toArray >>= fun r => pure r)
        (by simp) ?_
      refine Big.specR_callKH (C := ctxH C H3) cR fWCL wclParams [vv kFu, vv kC, vv kD, vv cV, vv cP, vv cQ, vv cB]
        (wclBody C) [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e', p2,
          (if whnfCoreCheapSafe h e then q3 else 0), BitVec.ofNat 64 f'] (by decide) rfl (by decide) hcl
        ⟨by simp [hFu], by simp [hC], by simp [hD0], by simp, by simp, by simp, by simp [hB], trivial⟩
        (hrec H3 s1 cheap d e' _ _ p2 _ hpc hq1 (lstAt_mono hpd p2 _ hl2) hl3') (fun r s2 H4 hp4 => ?_)
      refine specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ?_)
      exact ⟨H4, hpc.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · -- a memo hit
    have hne : optW (some x) ≠ 0 := WB.idxW_succ_ne x
    refine specR_ifI _ 1 (by simp [sev, hX, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_assignI cQ (.const 0) 0 (by decide) rfl ?_
    refine specR_assignI cV _ (Enc.idxW x) (by decide) (by simp [sev, hX, optWG, BitVec.add_sub_cancel]) ?_
    exact scRet_spec (σ := σ) (Γ := (cV, Enc.idxW x) :: (cQ, 0) :: Γ) (D := wclD) (s := s) hok hcf hcc hcodeS hcodeI
      hpre cheap xs [] p 0 x hp rfl (by simp [Env.get_cons, hC]) (by simp [Env.get_cons, hP]) (by simp [Env.get_cons])
      (by simp [Env.get_cons]) (by decide)

end

end ConPanqueque.T.WC
