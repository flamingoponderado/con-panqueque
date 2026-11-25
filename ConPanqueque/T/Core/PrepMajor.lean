import ConPanqueque.T.Core.MajorTests
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `prepareMajor`: the major premise's preparation, classified

`majorToCtor` (the classification, else the rescue callee and the fabrication's classification),
`prepareMajorWhnf` (`whnf`, `litMajorToCtor`, `majorToCtor`) and `prepareMajor` (the K path; the structure rescues
on the major as found, a `Nat.succ` application or a stuck major head-normalized). All answer `encMV`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def mcV := ofString "mcv"
def mcX := ofString "mcx"
def mcW := ofString "mcw"
def pwA := ofString "pwa"
def pwB := ofString "pwb"
def pwR := ofString "pwr"
def pmB := ofString "pmb"
def pmV := ofString "pmv"
def pmE := ofString "pme"
def pmS := ofString "pms"
def pmX := ofString "pmx"
def fMc := ofString "majorToCtor"
def fRs := ofString "majorToCtorRescue"
def fPw := ofString "prepareMajorWhnf"

@[simp] theorem pq_mcV_ne_mcX : mcV ≠ mcX := by decide
@[simp] theorem pq_mcV_ne_mcW : mcV ≠ mcW := by decide
@[simp] theorem pq_mcV_ne_pwA : mcV ≠ pwA := by decide
@[simp] theorem pq_mcV_ne_pwB : mcV ≠ pwB := by decide
@[simp] theorem pq_mcV_ne_pwR : mcV ≠ pwR := by decide
@[simp] theorem pq_mcV_ne_pmB : mcV ≠ pmB := by decide
@[simp] theorem pq_mcV_ne_pmV : mcV ≠ pmV := by decide
@[simp] theorem pq_mcV_ne_pmE : mcV ≠ pmE := by decide
@[simp] theorem pq_mcV_ne_pmS : mcV ≠ pmS := by decide
@[simp] theorem pq_mcV_ne_pmX : mcV ≠ pmX := by decide
@[simp] theorem pq_mcV_ne_kFu : mcV ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_mcV : kFu ≠ mcV := by decide
@[simp] theorem pq_mcV_ne_kD : mcV ≠ kD := by decide
@[simp] theorem pq_kD_ne_mcV : kD ≠ mcV := by decide
@[simp] theorem pq_mcV_ne_pmC : mcV ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_mcV : pmC ≠ mcV := by decide
@[simp] theorem pq_mcV_ne_pmK : mcV ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_mcV : pmK ≠ mcV := by decide
@[simp] theorem pq_mcV_ne_pmR : mcV ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_mcV : pmR ≠ mcV := by decide
@[simp] theorem pq_mcV_ne_pmM : mcV ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_mcV : pmM ≠ mcV := by decide
@[simp] theorem pq_mcX_ne_mcV : mcX ≠ mcV := by decide
@[simp] theorem pq_mcX_ne_mcW : mcX ≠ mcW := by decide
@[simp] theorem pq_mcX_ne_pwA : mcX ≠ pwA := by decide
@[simp] theorem pq_mcX_ne_pwB : mcX ≠ pwB := by decide
@[simp] theorem pq_mcX_ne_pwR : mcX ≠ pwR := by decide
@[simp] theorem pq_mcX_ne_pmB : mcX ≠ pmB := by decide
@[simp] theorem pq_mcX_ne_pmV : mcX ≠ pmV := by decide
@[simp] theorem pq_mcX_ne_pmE : mcX ≠ pmE := by decide
@[simp] theorem pq_mcX_ne_pmS : mcX ≠ pmS := by decide
@[simp] theorem pq_mcX_ne_pmX : mcX ≠ pmX := by decide
@[simp] theorem pq_mcX_ne_kFu : mcX ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_mcX : kFu ≠ mcX := by decide
@[simp] theorem pq_mcX_ne_kD : mcX ≠ kD := by decide
@[simp] theorem pq_kD_ne_mcX : kD ≠ mcX := by decide
@[simp] theorem pq_mcX_ne_pmC : mcX ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_mcX : pmC ≠ mcX := by decide
@[simp] theorem pq_mcX_ne_pmK : mcX ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_mcX : pmK ≠ mcX := by decide
@[simp] theorem pq_mcX_ne_pmR : mcX ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_mcX : pmR ≠ mcX := by decide
@[simp] theorem pq_mcX_ne_pmM : mcX ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_mcX : pmM ≠ mcX := by decide
@[simp] theorem pq_mcW_ne_mcV : mcW ≠ mcV := by decide
@[simp] theorem pq_mcW_ne_mcX : mcW ≠ mcX := by decide
@[simp] theorem pq_mcW_ne_pwA : mcW ≠ pwA := by decide
@[simp] theorem pq_mcW_ne_pwB : mcW ≠ pwB := by decide
@[simp] theorem pq_mcW_ne_pwR : mcW ≠ pwR := by decide
@[simp] theorem pq_mcW_ne_pmB : mcW ≠ pmB := by decide
@[simp] theorem pq_mcW_ne_pmV : mcW ≠ pmV := by decide
@[simp] theorem pq_mcW_ne_pmE : mcW ≠ pmE := by decide
@[simp] theorem pq_mcW_ne_pmS : mcW ≠ pmS := by decide
@[simp] theorem pq_mcW_ne_pmX : mcW ≠ pmX := by decide
@[simp] theorem pq_mcW_ne_kFu : mcW ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_mcW : kFu ≠ mcW := by decide
@[simp] theorem pq_mcW_ne_kD : mcW ≠ kD := by decide
@[simp] theorem pq_kD_ne_mcW : kD ≠ mcW := by decide
@[simp] theorem pq_mcW_ne_pmC : mcW ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_mcW : pmC ≠ mcW := by decide
@[simp] theorem pq_mcW_ne_pmK : mcW ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_mcW : pmK ≠ mcW := by decide
@[simp] theorem pq_mcW_ne_pmR : mcW ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_mcW : pmR ≠ mcW := by decide
@[simp] theorem pq_mcW_ne_pmM : mcW ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_mcW : pmM ≠ mcW := by decide
@[simp] theorem pq_pwA_ne_mcV : pwA ≠ mcV := by decide
@[simp] theorem pq_pwA_ne_mcX : pwA ≠ mcX := by decide
@[simp] theorem pq_pwA_ne_mcW : pwA ≠ mcW := by decide
@[simp] theorem pq_pwA_ne_pwB : pwA ≠ pwB := by decide
@[simp] theorem pq_pwA_ne_pwR : pwA ≠ pwR := by decide
@[simp] theorem pq_pwA_ne_pmB : pwA ≠ pmB := by decide
@[simp] theorem pq_pwA_ne_pmV : pwA ≠ pmV := by decide
@[simp] theorem pq_pwA_ne_pmE : pwA ≠ pmE := by decide
@[simp] theorem pq_pwA_ne_pmS : pwA ≠ pmS := by decide
@[simp] theorem pq_pwA_ne_pmX : pwA ≠ pmX := by decide
@[simp] theorem pq_pwA_ne_kFu : pwA ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pwA : kFu ≠ pwA := by decide
@[simp] theorem pq_pwA_ne_kD : pwA ≠ kD := by decide
@[simp] theorem pq_kD_ne_pwA : kD ≠ pwA := by decide
@[simp] theorem pq_pwA_ne_pmC : pwA ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pwA : pmC ≠ pwA := by decide
@[simp] theorem pq_pwA_ne_pmK : pwA ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pwA : pmK ≠ pwA := by decide
@[simp] theorem pq_pwA_ne_pmR : pwA ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pwA : pmR ≠ pwA := by decide
@[simp] theorem pq_pwA_ne_pmM : pwA ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pwA : pmM ≠ pwA := by decide
@[simp] theorem pq_pwB_ne_mcV : pwB ≠ mcV := by decide
@[simp] theorem pq_pwB_ne_mcX : pwB ≠ mcX := by decide
@[simp] theorem pq_pwB_ne_mcW : pwB ≠ mcW := by decide
@[simp] theorem pq_pwB_ne_pwA : pwB ≠ pwA := by decide
@[simp] theorem pq_pwB_ne_pwR : pwB ≠ pwR := by decide
@[simp] theorem pq_pwB_ne_pmB : pwB ≠ pmB := by decide
@[simp] theorem pq_pwB_ne_pmV : pwB ≠ pmV := by decide
@[simp] theorem pq_pwB_ne_pmE : pwB ≠ pmE := by decide
@[simp] theorem pq_pwB_ne_pmS : pwB ≠ pmS := by decide
@[simp] theorem pq_pwB_ne_pmX : pwB ≠ pmX := by decide
@[simp] theorem pq_pwB_ne_kFu : pwB ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pwB : kFu ≠ pwB := by decide
@[simp] theorem pq_pwB_ne_kD : pwB ≠ kD := by decide
@[simp] theorem pq_kD_ne_pwB : kD ≠ pwB := by decide
@[simp] theorem pq_pwB_ne_pmC : pwB ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pwB : pmC ≠ pwB := by decide
@[simp] theorem pq_pwB_ne_pmK : pwB ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pwB : pmK ≠ pwB := by decide
@[simp] theorem pq_pwB_ne_pmR : pwB ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pwB : pmR ≠ pwB := by decide
@[simp] theorem pq_pwB_ne_pmM : pwB ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pwB : pmM ≠ pwB := by decide
@[simp] theorem pq_pwR_ne_mcV : pwR ≠ mcV := by decide
@[simp] theorem pq_pwR_ne_mcX : pwR ≠ mcX := by decide
@[simp] theorem pq_pwR_ne_mcW : pwR ≠ mcW := by decide
@[simp] theorem pq_pwR_ne_pwA : pwR ≠ pwA := by decide
@[simp] theorem pq_pwR_ne_pwB : pwR ≠ pwB := by decide
@[simp] theorem pq_pwR_ne_pmB : pwR ≠ pmB := by decide
@[simp] theorem pq_pwR_ne_pmV : pwR ≠ pmV := by decide
@[simp] theorem pq_pwR_ne_pmE : pwR ≠ pmE := by decide
@[simp] theorem pq_pwR_ne_pmS : pwR ≠ pmS := by decide
@[simp] theorem pq_pwR_ne_pmX : pwR ≠ pmX := by decide
@[simp] theorem pq_pwR_ne_kFu : pwR ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pwR : kFu ≠ pwR := by decide
@[simp] theorem pq_pwR_ne_kD : pwR ≠ kD := by decide
@[simp] theorem pq_kD_ne_pwR : kD ≠ pwR := by decide
@[simp] theorem pq_pwR_ne_pmC : pwR ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pwR : pmC ≠ pwR := by decide
@[simp] theorem pq_pwR_ne_pmK : pwR ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pwR : pmK ≠ pwR := by decide
@[simp] theorem pq_pwR_ne_pmR : pwR ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pwR : pmR ≠ pwR := by decide
@[simp] theorem pq_pwR_ne_pmM : pwR ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pwR : pmM ≠ pwR := by decide
@[simp] theorem pq_pmB_ne_mcV : pmB ≠ mcV := by decide
@[simp] theorem pq_pmB_ne_mcX : pmB ≠ mcX := by decide
@[simp] theorem pq_pmB_ne_mcW : pmB ≠ mcW := by decide
@[simp] theorem pq_pmB_ne_pwA : pmB ≠ pwA := by decide
@[simp] theorem pq_pmB_ne_pwB : pmB ≠ pwB := by decide
@[simp] theorem pq_pmB_ne_pwR : pmB ≠ pwR := by decide
@[simp] theorem pq_pmB_ne_pmV : pmB ≠ pmV := by decide
@[simp] theorem pq_pmB_ne_pmE : pmB ≠ pmE := by decide
@[simp] theorem pq_pmB_ne_pmS : pmB ≠ pmS := by decide
@[simp] theorem pq_pmB_ne_pmX : pmB ≠ pmX := by decide
@[simp] theorem pq_pmB_ne_kFu : pmB ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pmB : kFu ≠ pmB := by decide
@[simp] theorem pq_pmB_ne_kD : pmB ≠ kD := by decide
@[simp] theorem pq_kD_ne_pmB : kD ≠ pmB := by decide
@[simp] theorem pq_pmB_ne_pmC : pmB ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pmB : pmC ≠ pmB := by decide
@[simp] theorem pq_pmB_ne_pmK : pmB ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pmB : pmK ≠ pmB := by decide
@[simp] theorem pq_pmB_ne_pmR : pmB ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pmB : pmR ≠ pmB := by decide
@[simp] theorem pq_pmB_ne_pmM : pmB ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pmB : pmM ≠ pmB := by decide
@[simp] theorem pq_pmV_ne_mcV : pmV ≠ mcV := by decide
@[simp] theorem pq_pmV_ne_mcX : pmV ≠ mcX := by decide
@[simp] theorem pq_pmV_ne_mcW : pmV ≠ mcW := by decide
@[simp] theorem pq_pmV_ne_pwA : pmV ≠ pwA := by decide
@[simp] theorem pq_pmV_ne_pwB : pmV ≠ pwB := by decide
@[simp] theorem pq_pmV_ne_pwR : pmV ≠ pwR := by decide
@[simp] theorem pq_pmV_ne_pmB : pmV ≠ pmB := by decide
@[simp] theorem pq_pmV_ne_pmE : pmV ≠ pmE := by decide
@[simp] theorem pq_pmV_ne_pmS : pmV ≠ pmS := by decide
@[simp] theorem pq_pmV_ne_pmX : pmV ≠ pmX := by decide
@[simp] theorem pq_pmV_ne_kFu : pmV ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pmV : kFu ≠ pmV := by decide
@[simp] theorem pq_pmV_ne_kD : pmV ≠ kD := by decide
@[simp] theorem pq_kD_ne_pmV : kD ≠ pmV := by decide
@[simp] theorem pq_pmV_ne_pmC : pmV ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pmV : pmC ≠ pmV := by decide
@[simp] theorem pq_pmV_ne_pmK : pmV ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pmV : pmK ≠ pmV := by decide
@[simp] theorem pq_pmV_ne_pmR : pmV ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pmV : pmR ≠ pmV := by decide
@[simp] theorem pq_pmV_ne_pmM : pmV ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pmV : pmM ≠ pmV := by decide
@[simp] theorem pq_pmE_ne_mcV : pmE ≠ mcV := by decide
@[simp] theorem pq_pmE_ne_mcX : pmE ≠ mcX := by decide
@[simp] theorem pq_pmE_ne_mcW : pmE ≠ mcW := by decide
@[simp] theorem pq_pmE_ne_pwA : pmE ≠ pwA := by decide
@[simp] theorem pq_pmE_ne_pwB : pmE ≠ pwB := by decide
@[simp] theorem pq_pmE_ne_pwR : pmE ≠ pwR := by decide
@[simp] theorem pq_pmE_ne_pmB : pmE ≠ pmB := by decide
@[simp] theorem pq_pmE_ne_pmV : pmE ≠ pmV := by decide
@[simp] theorem pq_pmE_ne_pmS : pmE ≠ pmS := by decide
@[simp] theorem pq_pmE_ne_pmX : pmE ≠ pmX := by decide
@[simp] theorem pq_pmE_ne_kFu : pmE ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pmE : kFu ≠ pmE := by decide
@[simp] theorem pq_pmE_ne_kD : pmE ≠ kD := by decide
@[simp] theorem pq_kD_ne_pmE : kD ≠ pmE := by decide
@[simp] theorem pq_pmE_ne_pmC : pmE ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pmE : pmC ≠ pmE := by decide
@[simp] theorem pq_pmE_ne_pmK : pmE ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pmE : pmK ≠ pmE := by decide
@[simp] theorem pq_pmE_ne_pmR : pmE ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pmE : pmR ≠ pmE := by decide
@[simp] theorem pq_pmE_ne_pmM : pmE ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pmE : pmM ≠ pmE := by decide
@[simp] theorem pq_pmS_ne_mcV : pmS ≠ mcV := by decide
@[simp] theorem pq_pmS_ne_mcX : pmS ≠ mcX := by decide
@[simp] theorem pq_pmS_ne_mcW : pmS ≠ mcW := by decide
@[simp] theorem pq_pmS_ne_pwA : pmS ≠ pwA := by decide
@[simp] theorem pq_pmS_ne_pwB : pmS ≠ pwB := by decide
@[simp] theorem pq_pmS_ne_pwR : pmS ≠ pwR := by decide
@[simp] theorem pq_pmS_ne_pmB : pmS ≠ pmB := by decide
@[simp] theorem pq_pmS_ne_pmV : pmS ≠ pmV := by decide
@[simp] theorem pq_pmS_ne_pmE : pmS ≠ pmE := by decide
@[simp] theorem pq_pmS_ne_pmX : pmS ≠ pmX := by decide
@[simp] theorem pq_pmS_ne_kFu : pmS ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pmS : kFu ≠ pmS := by decide
@[simp] theorem pq_pmS_ne_kD : pmS ≠ kD := by decide
@[simp] theorem pq_kD_ne_pmS : kD ≠ pmS := by decide
@[simp] theorem pq_pmS_ne_pmC : pmS ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pmS : pmC ≠ pmS := by decide
@[simp] theorem pq_pmS_ne_pmK : pmS ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pmS : pmK ≠ pmS := by decide
@[simp] theorem pq_pmS_ne_pmR : pmS ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pmS : pmR ≠ pmS := by decide
@[simp] theorem pq_pmS_ne_pmM : pmS ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pmS : pmM ≠ pmS := by decide
@[simp] theorem pq_pmX_ne_mcV : pmX ≠ mcV := by decide
@[simp] theorem pq_pmX_ne_mcX : pmX ≠ mcX := by decide
@[simp] theorem pq_pmX_ne_mcW : pmX ≠ mcW := by decide
@[simp] theorem pq_pmX_ne_pwA : pmX ≠ pwA := by decide
@[simp] theorem pq_pmX_ne_pwB : pmX ≠ pwB := by decide
@[simp] theorem pq_pmX_ne_pwR : pmX ≠ pwR := by decide
@[simp] theorem pq_pmX_ne_pmB : pmX ≠ pmB := by decide
@[simp] theorem pq_pmX_ne_pmV : pmX ≠ pmV := by decide
@[simp] theorem pq_pmX_ne_pmE : pmX ≠ pmE := by decide
@[simp] theorem pq_pmX_ne_pmS : pmX ≠ pmS := by decide
@[simp] theorem pq_pmX_ne_kFu : pmX ≠ kFu := by decide
@[simp] theorem pq_kFu_ne_pmX : kFu ≠ pmX := by decide
@[simp] theorem pq_pmX_ne_kD : pmX ≠ kD := by decide
@[simp] theorem pq_kD_ne_pmX : kD ≠ pmX := by decide
@[simp] theorem pq_pmX_ne_pmC : pmX ≠ pmC := by decide
@[simp] theorem pq_pmC_ne_pmX : pmC ≠ pmX := by decide
@[simp] theorem pq_pmX_ne_pmK : pmX ≠ pmK := by decide
@[simp] theorem pq_pmK_ne_pmX : pmK ≠ pmX := by decide
@[simp] theorem pq_pmX_ne_pmR : pmX ≠ pmR := by decide
@[simp] theorem pq_pmR_ne_pmX : pmR ≠ pmX := by decide
@[simp] theorem pq_pmX_ne_pmM : pmX ≠ pmM := by decide
@[simp] theorem pq_pmM_ne_pmX : pmM ≠ pmX := by decide

def mcLocals : List MlS := [mcV, mcX, mcW]
def mcBody : ProgHOL 64 := prologue mcLocals
  (.seq (.call (some (some (.local, mcV), none)) fCw [vv pmM])
    (.ite (.op .and [vv mcV, .const 1]) (.return (vv mcV))
    (.seq (.call (some (some (.local, mcX), none)) fRs [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM])
    (.ite (.cmp .equal (vv mcX) (vv pmM)) (.return (.shift .lsl (vv pmM) (.const 1)))
    (.seq (.call (some (some (.local, mcW), none)) fCw [vv mcX])
    (.return (vv mcW)))))))

def pwLocals : List MlS := [pwA, pwB, pwR]
def pwBody : ProgHOL 64 := prologue pwLocals
  (.seq (.call (some (some (.local, pwA), none)) fW [vv kFu, vv kD, vv pmM])
    (.seq (.call (some (some (.local, pwB), none)) fLm [vv kFu, vv kD, vv pwA])
    (.seq (.call (some (some (.local, pwR), none)) fMc [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pwB])
    (.return (vv pwR)))))

def pmLocals : List MlS := [pmB, pmV, pmE, pmS, pmX]
def pmBody : ProgHOL 64 := prologue pmLocals
  (.ite (vv pmK)
    (.seq (.call (some (some (.local, pmX), none)) fMc [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM])
    (.return (vv pmX)))
    (.seq (.call (some (some (.local, pmB), none)) fIsl [vv pmM])
    (.ite (vv pmB)
    (.seq (.assign .local pmV (.shift .lsl (vv pmM) (.const 1)))
    (.ite (.op .and [vv pmV, .const 1])
    (.seq (.assign .local pmE (.shift .lsr (vv pmV) (.const 1)))
    (.seq (.call (some (some (.local, pmS), none)) fNs [vv pmE])
    (.ite (vv pmS)
    (.seq (.call (some (some (.local, pmX), none)) fPw [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE])
    (.return (vv pmX)))
    (.return (vv pmV)))))
    (.seq (.assign .local pmE (.shift .lsr (vv pmV) (.const 1)))
    (.seq (.call (some (some (.local, pmX), none)) fPw [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE])
    (.return (vv pmX))))))
    (.seq (.call (some (some (.local, pmV), none)) fMc [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM])
    (.ite (.op .and [vv pmV, .const 1])
    (.seq (.assign .local pmE (.shift .lsr (vv pmV) (.const 1)))
    (.seq (.call (some (some (.local, pmS), none)) fNs [vv pmE])
    (.ite (vv pmS)
    (.seq (.call (some (some (.local, pmX), none)) fPw [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE])
    (.return (vv pmX)))
    (.return (vv pmV)))))
    (.seq (.assign .local pmE (.shift .lsr (vv pmV) (.const 1)))
    (.seq (.call (some (some (.local, pmX), none)) fPw [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE])
    (.return (vv pmX)))))))))

section
variable {σ : Type}

theorem postMV_locals (C : Ctx) : ∀ (a : MajorView) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostMV C a w s' st → PostMV C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem mc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mcLocals → (ctxEnv C ++ pmParams.zip vals).get x = none :=
  Knot.params_none C mcLocals pmParams vals (by decide) (by decide)
theorem pw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pwLocals → (ctxEnv C ++ pmParams.zip vals).get x = none :=
  Knot.params_none C pwLocals pmParams vals (by decide) (by decide)
theorem pm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pmLocals → (ctxEnv C ++ pmParams.zip vals).get x = none :=
  Knot.params_none C pmLocals pmParams vals (by decide) (by decide)

/-- The code the classification calls. -/
structure CwCodes (C : Ctx) : Prop where
  cw : C.code.lookup fCw = some ([(cwE, ShapeHOL.one)], cwBody C, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)

theorem mc_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : CwCodes C) (Brs : ProgHOL 64)
    (hcr : C.code.lookup fRs = some (pmParams.map (fun p => (p, ShapeHOL.one)), Brs, .one))
    (s : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule) (rw : BitVec 64) (m : EIdx)
    (hRs : ∀ (H : List (BitVec 64)) s1, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
        Enc.idxW m])) Brs s1 (majorToCtorRescue mode (knot mode C n) C.fe d c isK rules m) (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
      Enc.idxW m])) mcBody s (majorToCtor mode (knot mode C n) C.fe d c isK rules m) (PostMV C) := by
  refine specR_prologue (postMV_locals C) (mc_none C _) ?_
  unfold majorToCtor
  refine specR_callNIH mcV fCw [cwE] [vv pmM] (cwBody C) [Enc.idxW m] (by decide) rfl (by decide) hc.cw
    ⟨by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩ (PostMV C) (fun v w _ _ => w = encMV v)
    (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [cwE] _ rfl hlk)
      (cw_spec C hok hc.af hc.mg hc.mp s m)) (fun v w s1 H1 hp1 hw => ?_)
  subst hw
  cases hct : v.isCtor
  · refine specR_ifI _ 0 (by simp [sev, encMV_and1, hct]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ite_false]
    refine specR_callKH (C := ctxH C H1) mcX fRs pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM] Brs
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw, Enc.idxW m] (by decide) rfl (by decide) hcr
      ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
        by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
        by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
      (hRs H1 s1 hp1) (fun x s2 H2 hp2 => ?_)
    by_cases hx : x = m
    · subst hx
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [ite_eq_left (by simp)]
      exact specR_returnI _ (encMV (.stuck x)) (by simp +decide [sev, Env.get, pmParams, ctxEnv, encMV_stuck])
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW x ≠ Enc.idxW m := fun e => hx (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [ite_eq_right (by simpa using hx)]
      refine specR_congr (m' := ctorView C.fe x >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) mcW fCw [cwE] [vv mcX] (cwBody C) [Enc.idxW x] (by decide) rfl (by decide)
        hc.cw ⟨by simp, trivial⟩ (PostMV (ctxH C H2)) (fun v w _ _ => w = encMV v)
        (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [cwE] _ rfl hlk)
          (cw_spec (ctxH C H2) (ctxOK_H hok H2) hc.af hc.mg hc.mp s2 x)) (fun v' w s3 H3 hp3 hw => ?_)
      subst hw
      exact specR_returnI _ (encMV v') (by simp)
        (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [sev, encMV_and1, hct]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [ite_true]
    exact specR_returnI _ (encMV v) (by simp)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem tcCodes_H {C : Ctx} (hc : TcCodes C) (H : List (BitVec 64)) : TcCodes (ctxH C H) :=
  ⟨slCodes_H hc.sl H, hc.lit, hc.ls, hc.ic⟩
theorem nlCodes_H {C : Ctx} (hc : NlCodes C) (H : List (BitVec 64)) : NlCodes (ctxH C H) :=
  ⟨hc.lit, hc.ic, hc.sub, hc.litb, hc.ia⟩
theorem cwCodes_H {C : Ctx} (hc : CwCodes C) (H : List (BitVec 64)) : CwCodes (ctxH C H) :=
  ⟨hc.cw, hc.af, hc.mg, hc.mp⟩

/-- The code the major's preparation calls. -/
structure PmCodes (C : Ctx) (Brs : ProgHOL 64) : Prop where
  tc : TcCodes C
  nl : NlCodes C
  cw : CwCodes C
  nlf : C.code.lookup fNl = some ([(nlH, ShapeHOL.one)], nlBody C, .one)
  tcf : C.code.lookup fTc = some ([(tcH, ShapeHOL.one)], tcBody C, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  lm : C.code.lookup fLm = some (kParams.map (fun p => (p, ShapeHOL.one)), lmBody, .one)
  mc : C.code.lookup fMc = some (pmParams.map (fun p => (p, ShapeHOL.one)), mcBody, .one)
  rs : C.code.lookup fRs = some (pmParams.map (fun p => (p, ShapeHOL.one)), Brs, .one)
  pw : C.code.lookup fPw = some (pmParams.map (fun p => (p, ShapeHOL.one)), pwBody, .one)
  isl : C.code.lookup fIsl = some ([(isH, ShapeHOL.one)], islBody, .one)
  ns : C.code.lookup fNs = some ([(nsE, ShapeHOL.one)], nsBody C, .one)

theorem pmCodes_H {C : Ctx} {Brs : ProgHOL 64} (hc : PmCodes C Brs) (H : List (BitVec 64)) : PmCodes (ctxH C H) Brs :=
  ⟨tcCodes_H hc.tc H, nlCodes_H hc.nl H, cwCodes_H hc.cw H, hc.nlf, hc.tcf, hc.w, hc.lm, hc.mc, hc.rs, hc.pw, hc.isl,
    hc.ns⟩

theorem pw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Brs : ProgHOL 64) (hc : PmCodes C Brs)
    (s : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule) (rw : BitVec 64) (m : EIdx)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hRs : ∀ (m' : EIdx) (H : List (BitVec 64)) s1, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
        Enc.idxW m'])) Brs s1 (majorToCtorRescue mode (knot mode C n) C.fe d c isK rules m') (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
      Enc.idxW m])) pwBody s (prepareMajorWhnf mode (knot mode C n) C.fe d c isK rules m) (PostMV C) := by
  refine specR_prologue (postMV_locals C) (pw_none C _) ?_
  unfold prepareMajorWhnf
  refine Big.specR_callKC pwA fW kParams [vv kFu, vv kD, vv pmM] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW m] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
      by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩ (hW C.H s (List.prefix_refl _) m)
    (fun m0 s1 H1 hp1 _ => ?_)
  have hok1 := ctxOK_H hok H1
  refine specR_callKH (C := ctxH C H1) pwB fLm kParams [vv kFu, vv kD, vv pwA] lmBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW m0] (by decide) rfl (by decide) hc.lm
    ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
    (lm_spec ra mode n (ctxH C H1) hok1 (tcCodes_H hc.tc H1) (nlCodes_H hc.nl H1) hc.nlf hc.tcf hc.w s1 d m0
      (fun H s2 hp e' => hW H s2 (hp1.trans hp) e')) (fun m1 s2 H2 hp2 => ?_)
  have hok2 := ctxOK_H hok H2
  refine specR_congr (m' := majorToCtor mode (knot mode C n) C.fe d c isK rules m1 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H2) pwR fMc pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pwB] mcBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw, Enc.idxW m1] (by decide) rfl (by decide) hc.mc
    ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
      by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
      by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
    (PostMV (ctxH C H2)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
      (mc_spec mode n (ctxH C H2) hok2 (cwCodes_H hc.cw H2) Brs hc.rs s2 d c isK rules rw m1
        (fun H s3 hp => hRs m1 H s3 ((hp1.trans hp2).trans hp))))
    (fun v w s3 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ (encMV v) (by simp)
    (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem pm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Brs : ProgHOL 64) (hc : PmCodes C Brs)
    (s : AState) (d : Nat) (c : NIdx) (isK' : Bool) (rules : List IRecRule) (rw : BitVec 64) (m : EIdx)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hRs : ∀ (m' : EIdx) (H : List (BitVec 64)) s1, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK',
        rw, Enc.idxW m'])) Brs s1 (majorToCtorRescue mode (knot mode C n) C.fe d c isK' rules m')
        (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK', rw,
      Enc.idxW m])) pmBody s (prepareMajor mode (knot mode C n) C.fe d c isK' rules m) (PostMV C) := by
  refine specR_prologue (postMV_locals C) (pm_none C _) ?_
  unfold prepareMajor
  cases isK'
  · refine specR_ifI _ 0 (by simp +decide [Env.get, pmParams, ctxEnv, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ite_false]
    refine specR_callNIH pmB fIsl [isH] [vv pmM] islBody [Enc.idxW m] (by decide) rfl (by decide) hc.isl
      ⟨by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩ (Knot.PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [isH] _ rfl hlk) (isl_spec C s m))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    cases b
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ite_false]
      refine specR_callNIH (C := ctxH C H1) pmV fMc pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM] mcBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW false, rw, Enc.idxW m] (by decide) rfl (by decide)
        hc.mc ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
          by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
          by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
        (PostMV (ctxH C H1)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
          (mc_spec mode n (ctxH C H1) (ctxOK_H hok H1) (cwCodes_H hc.cw H1) Brs hc.rs s1 d c false rules rw m
            (fun H s2 hp => hRs m H s2 (hp1.trans hp))))
        (fun vE w s2 H2 hp2 hw => ?_)
      subst hw
      have hpX : C.H <+: H2 := hp1.trans hp2
      cases hct : vE.isCtor
      · refine specR_ifI _ 0 (by simp [sev, encMV_and1, hct]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [hct, Bool.false_eq_true, ite_false]
        refine specR_assignI pmE _ (Enc.idxW vE.expr) (by decide) (by simp [sev]; exact encMV_shr1 _) ?_
        refine specR_bindPure ?_
        refine specR_callNIH (C := ctxH C H2) pmX fPw pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE] pwBody
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW false, rw, Enc.idxW vE.expr] (by decide) rfl
          (by decide) hc.pw
          ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
            by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
            by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
          (PostMV (ctxH C H2)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
            (pw_spec ra mode n (ctxH C H2) (ctxOK_H hok H2) Brs (pmCodes_H hc H2) s2 d c false rules rw vE.expr
              (fun H s2 hp e' => hW H s2 (hpX.trans hp) e') (fun m' H s2 hp => hRs m' H s2 (hpX.trans hp))))
          (fun v' w s3 H3 hp3 hw => ?_)
        subst hw
        exact specR_returnI _ (encMV v') (by simp)
          (fun t ht => ⟨H3, hpX.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, encMV_and1, hct]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [hct, ite_true]
        refine specR_assignI pmE _ (Enc.idxW vE.expr) (by decide) (by simp [sev]; exact encMV_shr1 _) ?_
        refine specR_callNIH (C := ctxH C H2) pmS fNs [nsE] [vv pmE] (nsBody C) [Enc.idxW vE.expr] (by decide) rfl
          (by decide) hc.ns ⟨by simp, trivial⟩ (Knot.PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
          (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nsE] _ rfl hlk)
            (ns_spec (ctxH C H2) (ctxOK_H hok H2) s2 vE.expr))
          (fun b w s3 H3 hp3 hw => ?_)
        subst hw
        have hpX3 : C.H <+: H3 := hpX.trans hp3
        cases b
        · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
          simp only [Bool.false_eq_true, ite_false]
          exact specR_returnI _ (encMV vE) (by simp)
            (fun t ht => ⟨H3, hpX3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
          simp only [ite_true]
          refine specR_bindPure ?_
          refine specR_callNIH (C := ctxH C H3) pmX fPw pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE] pwBody
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW false, rw, Enc.idxW vE.expr] (by decide) rfl
            (by decide) hc.pw
            ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
            (PostMV (ctxH C H3)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
              (pw_spec ra mode n (ctxH C H3) (ctxOK_H hok H3) Brs (pmCodes_H hc H3) s3 d c false rules rw vE.expr
                (fun H s2 hp e' => hW H s2 (hpX3.trans hp) e') (fun m' H s2 hp => hRs m' H s2 (hpX3.trans hp))))
            (fun v' w s4 H4 hp4 hw => ?_)
          subst hw
          exact specR_returnI _ (encMV v') (by simp)
            (fun t ht => ⟨H4, hpX3.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ite_true, pure_bind]
      refine specR_assignI pmV _ (encMV (.stuck m)) (by decide)
        (by simp +decide [sev, Env.get, pmParams, ctxEnv, encMV_stuck]) ?_
      have hpX : C.H <+: H1 := hp1
      cases hct : (MajorView.stuck m).isCtor
      · refine specR_ifI _ 0 (by simp [sev, encMV_and1, hct]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [hct, Bool.false_eq_true, ite_false]
        refine specR_assignI pmE _ (Enc.idxW (MajorView.stuck m).expr) (by decide) (by simp [sev]; exact encMV_shr1 _) ?_
        refine specR_bindPure ?_
        refine specR_callNIH (C := ctxH C H1) pmX fPw pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE] pwBody
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW false, rw, Enc.idxW (MajorView.stuck m).expr] (by decide) rfl
          (by decide) hc.pw
          ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
            by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
            by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
          (PostMV (ctxH C H1)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
            (pw_spec ra mode n (ctxH C H1) (ctxOK_H hok H1) Brs (pmCodes_H hc H1) s1 d c false rules rw (MajorView.stuck m).expr
              (fun H s2 hp e' => hW H s2 (hpX.trans hp) e') (fun m' H s2 hp => hRs m' H s2 (hpX.trans hp))))
          (fun v' w s3 H3 hp3 hw => ?_)
        subst hw
        exact specR_returnI _ (encMV v') (by simp)
          (fun t ht => ⟨H3, hpX.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, encMV_and1, hct]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [hct, ite_true]
        refine specR_assignI pmE _ (Enc.idxW (MajorView.stuck m).expr) (by decide) (by simp [sev]; exact encMV_shr1 _) ?_
        refine specR_callNIH (C := ctxH C H1) pmS fNs [nsE] [vv pmE] (nsBody C) [Enc.idxW (MajorView.stuck m).expr] (by decide) rfl
          (by decide) hc.ns ⟨by simp, trivial⟩ (Knot.PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
          (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nsE] _ rfl hlk)
            (ns_spec (ctxH C H1) (ctxOK_H hok H1) s1 (MajorView.stuck m).expr))
          (fun b w s3 H3 hp3 hw => ?_)
        subst hw
        have hpX3 : C.H <+: H3 := hpX.trans hp3
        cases b
        · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
          simp only [Bool.false_eq_true, ite_false]
          exact specR_returnI _ (encMV (MajorView.stuck m)) (by simp)
            (fun t ht => ⟨H3, hpX3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
          simp only [ite_true]
          refine specR_bindPure ?_
          refine specR_callNIH (C := ctxH C H3) pmX fPw pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmE] pwBody
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW false, rw, Enc.idxW (MajorView.stuck m).expr] (by decide) rfl
            (by decide) hc.pw
            ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp +decide [Env.get, pmParams, ctxEnv], by simp, trivial⟩
            (PostMV (ctxH C H3)) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
              (pw_spec ra mode n (ctxH C H3) (ctxOK_H hok H3) Brs (pmCodes_H hc H3) s3 d c false rules rw (MajorView.stuck m).expr
                (fun H s2 hp e' => hW H s2 (hpX3.trans hp) e') (fun m' H s2 hp => hRs m' H s2 (hpX3.trans hp))))
            (fun v' w s4 H4 hp4 hw => ?_)
          subst hw
          exact specR_returnI _ (encMV v') (by simp)
            (fun t ht => ⟨H4, hpX3.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp +decide [Env.get, pmParams, ctxEnv, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [ite_true]
    refine specR_congr (m' := majorToCtor mode (knot mode C n) C.fe d c true rules m >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH pmX fMc pmParams [vv kFu, vv kD, vv pmC, vv pmK, vv pmR, vv pmM] mcBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW true, rw, Enc.idxW m] (by decide) rfl (by decide)
      hc.mc ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
        by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
        by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
      (PostMV C) (fun v w _ _ => w = encMV v) (fun v w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (mc_spec mode n C hok hc.cw Brs hc.rs s d c true rules rw m
          (fun H s2 hp => hRs m H s2 hp)))
      (fun v w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI _ (encMV v) (by simp) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
