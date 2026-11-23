import ConPanqueque.T.Core.Wscoped
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `hasLooseBVarInGo`

Does a loose bound variable of index `d ..< d + w` occur? The twin's memoized walk: the packed-bound cutoff
(`looseBVarsBounded`, i.e. `bvarB ≤ d`), the leaves, then the memo (a heap memo list, as `wscopedBGo`'s) and the
short-circuiting arms (a binder body at `d + 1`); each answer is a fresh pair block `[answer, memo]`. The cutoff
may update the twin's caches, so the state is threaded.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def hvF := ofString "hvn_f"
def hvW := ofString "hvn_w"
def hvD := ofString "hvn_d"
def hvH := ofString "hvn_h"
def hvM := ofString "hvn_m"
def hvC0 := ofString "hvn_c0"
def hvJ := ofString "hvn_j"
def hvL := ofString "hvn_l"
def hvC1 := ofString "hvn_c1"
def hvC2 := ofString "hvn_c2"
def hvC3 := ofString "hvn_c3"
def hvR := ofString "hvn_r"
def hvM2 := ofString "hvn_m2"
def hvK1 := ofString "hvn_k1"
def hvK2 := ofString "hvn_k2"
def hvK3 := ofString "hvn_k3"
def hvN := ofString "hvn_n"
def hvO := ofString "hvn_o"
/-- `hasLooseBVarInGo` with the fuel-exhaustion message a parameter: `hasLooseBVarBGo` is its window-`1` case. -/
def hlGo (msg : String) (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) :
    Nat → EIdx → AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | 0, _ => fail (.internal msg)
  | fuel + 1, h => do
    let bb ← bvarB fuel h
    if bb ≤ d then pure (false, memo) else
    match ← view h with
    | .bvar j => pure (decide (d ≤ j) && decide (j - d < w), memo)
    | .fvar _ _ => pure (false, memo)
    | .sort _ => pure (false, memo)
    | .const _ _ => pure (false, memo)
    | .lit _ => pure (false, memo)
    | v =>
      match memo[(h, d)]? with
      | some r => pure (r, memo)
      | none => do
        let r ← match v with
          | .app f a => do
            match ← hlGo msg memo w d fuel f with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hlGo msg memo w d fuel a
          | .lam ty b => do
            match ← hlGo msg memo w d fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hlGo msg memo w (d + 1) fuel b
          | .forallE ty b => do
            match ← hlGo msg memo w d fuel ty with
            | (true, memo) => pure (true, memo)
            | (false, memo) => hlGo msg memo w (d + 1) fuel b
          | .letE t v b => do
            match ← hlGo msg memo w d fuel t with
            | (true, memo) => pure (true, memo)
            | (false, memo) => do
              match ← hlGo msg memo w d fuel v with
              | (true, memo) => pure (true, memo)
              | (false, memo) => hlGo msg memo w (d + 1) fuel b
          | .proj _ _ sub => hlGo msg memo w d fuel sub
          | _ => pure (false, memo)
        pure (hasLooseBVarBIns h d r)

def fHv := ofString "hasLooseBVarInGo"

@[simp] theorem hv_hvF_ne_hvW : hvF ≠ hvW := by decide
@[simp] theorem hv_hvF_ne_hvD : hvF ≠ hvD := by decide
@[simp] theorem hv_hvF_ne_hvH : hvF ≠ hvH := by decide
@[simp] theorem hv_hvF_ne_hvM : hvF ≠ hvM := by decide
@[simp] theorem hv_hvF_ne_hvC0 : hvF ≠ hvC0 := by decide
@[simp] theorem hv_hvF_ne_hvJ : hvF ≠ hvJ := by decide
@[simp] theorem hv_hvF_ne_hvL : hvF ≠ hvL := by decide
@[simp] theorem hv_hvF_ne_hvC1 : hvF ≠ hvC1 := by decide
@[simp] theorem hv_hvF_ne_hvC2 : hvF ≠ hvC2 := by decide
@[simp] theorem hv_hvF_ne_hvC3 : hvF ≠ hvC3 := by decide
@[simp] theorem hv_hvF_ne_hvR : hvF ≠ hvR := by decide
@[simp] theorem hv_hvF_ne_hvM2 : hvF ≠ hvM2 := by decide
@[simp] theorem hv_hvF_ne_hvK1 : hvF ≠ hvK1 := by decide
@[simp] theorem hv_hvF_ne_hvK2 : hvF ≠ hvK2 := by decide
@[simp] theorem hv_hvF_ne_hvK3 : hvF ≠ hvK3 := by decide
@[simp] theorem hv_hvF_ne_hvN : hvF ≠ hvN := by decide
@[simp] theorem hv_hvF_ne_hvO : hvF ≠ hvO := by decide
@[simp] theorem hv_hvF_ne_lFl : hvF ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvF : lFl ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lDh : hvF ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvF : lDh ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lDt : hvF ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvF : lDt ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lDg : hvF ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvF : lDg ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lDi : hvF ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvF : lDi ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lRp : hvF ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvF : lRp ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lRn : hvF ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvF : lRn ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lDir : hvF ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvF : lDir ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lFle : hvF ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvF : lFle ≠ hvF := by decide
@[simp] theorem hv_hvF_ne_lKb : hvF ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvF : lKb ≠ hvF := by decide
@[simp] theorem hv_hvW_ne_hvF : hvW ≠ hvF := by decide
@[simp] theorem hv_hvW_ne_hvD : hvW ≠ hvD := by decide
@[simp] theorem hv_hvW_ne_hvH : hvW ≠ hvH := by decide
@[simp] theorem hv_hvW_ne_hvM : hvW ≠ hvM := by decide
@[simp] theorem hv_hvW_ne_hvC0 : hvW ≠ hvC0 := by decide
@[simp] theorem hv_hvW_ne_hvJ : hvW ≠ hvJ := by decide
@[simp] theorem hv_hvW_ne_hvL : hvW ≠ hvL := by decide
@[simp] theorem hv_hvW_ne_hvC1 : hvW ≠ hvC1 := by decide
@[simp] theorem hv_hvW_ne_hvC2 : hvW ≠ hvC2 := by decide
@[simp] theorem hv_hvW_ne_hvC3 : hvW ≠ hvC3 := by decide
@[simp] theorem hv_hvW_ne_hvR : hvW ≠ hvR := by decide
@[simp] theorem hv_hvW_ne_hvM2 : hvW ≠ hvM2 := by decide
@[simp] theorem hv_hvW_ne_hvK1 : hvW ≠ hvK1 := by decide
@[simp] theorem hv_hvW_ne_hvK2 : hvW ≠ hvK2 := by decide
@[simp] theorem hv_hvW_ne_hvK3 : hvW ≠ hvK3 := by decide
@[simp] theorem hv_hvW_ne_hvN : hvW ≠ hvN := by decide
@[simp] theorem hv_hvW_ne_hvO : hvW ≠ hvO := by decide
@[simp] theorem hv_hvW_ne_lFl : hvW ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvW : lFl ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lDh : hvW ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvW : lDh ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lDt : hvW ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvW : lDt ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lDg : hvW ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvW : lDg ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lDi : hvW ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvW : lDi ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lRp : hvW ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvW : lRp ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lRn : hvW ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvW : lRn ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lDir : hvW ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvW : lDir ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lFle : hvW ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvW : lFle ≠ hvW := by decide
@[simp] theorem hv_hvW_ne_lKb : hvW ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvW : lKb ≠ hvW := by decide
@[simp] theorem hv_hvD_ne_hvF : hvD ≠ hvF := by decide
@[simp] theorem hv_hvD_ne_hvW : hvD ≠ hvW := by decide
@[simp] theorem hv_hvD_ne_hvH : hvD ≠ hvH := by decide
@[simp] theorem hv_hvD_ne_hvM : hvD ≠ hvM := by decide
@[simp] theorem hv_hvD_ne_hvC0 : hvD ≠ hvC0 := by decide
@[simp] theorem hv_hvD_ne_hvJ : hvD ≠ hvJ := by decide
@[simp] theorem hv_hvD_ne_hvL : hvD ≠ hvL := by decide
@[simp] theorem hv_hvD_ne_hvC1 : hvD ≠ hvC1 := by decide
@[simp] theorem hv_hvD_ne_hvC2 : hvD ≠ hvC2 := by decide
@[simp] theorem hv_hvD_ne_hvC3 : hvD ≠ hvC3 := by decide
@[simp] theorem hv_hvD_ne_hvR : hvD ≠ hvR := by decide
@[simp] theorem hv_hvD_ne_hvM2 : hvD ≠ hvM2 := by decide
@[simp] theorem hv_hvD_ne_hvK1 : hvD ≠ hvK1 := by decide
@[simp] theorem hv_hvD_ne_hvK2 : hvD ≠ hvK2 := by decide
@[simp] theorem hv_hvD_ne_hvK3 : hvD ≠ hvK3 := by decide
@[simp] theorem hv_hvD_ne_hvN : hvD ≠ hvN := by decide
@[simp] theorem hv_hvD_ne_hvO : hvD ≠ hvO := by decide
@[simp] theorem hv_hvD_ne_lFl : hvD ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvD : lFl ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lDh : hvD ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvD : lDh ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lDt : hvD ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvD : lDt ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lDg : hvD ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvD : lDg ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lDi : hvD ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvD : lDi ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lRp : hvD ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvD : lRp ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lRn : hvD ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvD : lRn ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lDir : hvD ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvD : lDir ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lFle : hvD ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvD : lFle ≠ hvD := by decide
@[simp] theorem hv_hvD_ne_lKb : hvD ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvD : lKb ≠ hvD := by decide
@[simp] theorem hv_hvH_ne_hvF : hvH ≠ hvF := by decide
@[simp] theorem hv_hvH_ne_hvW : hvH ≠ hvW := by decide
@[simp] theorem hv_hvH_ne_hvD : hvH ≠ hvD := by decide
@[simp] theorem hv_hvH_ne_hvM : hvH ≠ hvM := by decide
@[simp] theorem hv_hvH_ne_hvC0 : hvH ≠ hvC0 := by decide
@[simp] theorem hv_hvH_ne_hvJ : hvH ≠ hvJ := by decide
@[simp] theorem hv_hvH_ne_hvL : hvH ≠ hvL := by decide
@[simp] theorem hv_hvH_ne_hvC1 : hvH ≠ hvC1 := by decide
@[simp] theorem hv_hvH_ne_hvC2 : hvH ≠ hvC2 := by decide
@[simp] theorem hv_hvH_ne_hvC3 : hvH ≠ hvC3 := by decide
@[simp] theorem hv_hvH_ne_hvR : hvH ≠ hvR := by decide
@[simp] theorem hv_hvH_ne_hvM2 : hvH ≠ hvM2 := by decide
@[simp] theorem hv_hvH_ne_hvK1 : hvH ≠ hvK1 := by decide
@[simp] theorem hv_hvH_ne_hvK2 : hvH ≠ hvK2 := by decide
@[simp] theorem hv_hvH_ne_hvK3 : hvH ≠ hvK3 := by decide
@[simp] theorem hv_hvH_ne_hvN : hvH ≠ hvN := by decide
@[simp] theorem hv_hvH_ne_hvO : hvH ≠ hvO := by decide
@[simp] theorem hv_hvH_ne_lFl : hvH ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvH : lFl ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lDh : hvH ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvH : lDh ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lDt : hvH ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvH : lDt ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lDg : hvH ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvH : lDg ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lDi : hvH ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvH : lDi ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lRp : hvH ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvH : lRp ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lRn : hvH ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvH : lRn ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lDir : hvH ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvH : lDir ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lFle : hvH ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvH : lFle ≠ hvH := by decide
@[simp] theorem hv_hvH_ne_lKb : hvH ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvH : lKb ≠ hvH := by decide
@[simp] theorem hv_hvM_ne_hvF : hvM ≠ hvF := by decide
@[simp] theorem hv_hvM_ne_hvW : hvM ≠ hvW := by decide
@[simp] theorem hv_hvM_ne_hvD : hvM ≠ hvD := by decide
@[simp] theorem hv_hvM_ne_hvH : hvM ≠ hvH := by decide
@[simp] theorem hv_hvM_ne_hvC0 : hvM ≠ hvC0 := by decide
@[simp] theorem hv_hvM_ne_hvJ : hvM ≠ hvJ := by decide
@[simp] theorem hv_hvM_ne_hvL : hvM ≠ hvL := by decide
@[simp] theorem hv_hvM_ne_hvC1 : hvM ≠ hvC1 := by decide
@[simp] theorem hv_hvM_ne_hvC2 : hvM ≠ hvC2 := by decide
@[simp] theorem hv_hvM_ne_hvC3 : hvM ≠ hvC3 := by decide
@[simp] theorem hv_hvM_ne_hvR : hvM ≠ hvR := by decide
@[simp] theorem hv_hvM_ne_hvM2 : hvM ≠ hvM2 := by decide
@[simp] theorem hv_hvM_ne_hvK1 : hvM ≠ hvK1 := by decide
@[simp] theorem hv_hvM_ne_hvK2 : hvM ≠ hvK2 := by decide
@[simp] theorem hv_hvM_ne_hvK3 : hvM ≠ hvK3 := by decide
@[simp] theorem hv_hvM_ne_hvN : hvM ≠ hvN := by decide
@[simp] theorem hv_hvM_ne_hvO : hvM ≠ hvO := by decide
@[simp] theorem hv_hvM_ne_lFl : hvM ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvM : lFl ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lDh : hvM ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvM : lDh ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lDt : hvM ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvM : lDt ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lDg : hvM ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvM : lDg ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lDi : hvM ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvM : lDi ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lRp : hvM ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvM : lRp ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lRn : hvM ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvM : lRn ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lDir : hvM ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvM : lDir ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lFle : hvM ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvM : lFle ≠ hvM := by decide
@[simp] theorem hv_hvM_ne_lKb : hvM ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvM : lKb ≠ hvM := by decide
@[simp] theorem hv_hvC0_ne_hvF : hvC0 ≠ hvF := by decide
@[simp] theorem hv_hvC0_ne_hvW : hvC0 ≠ hvW := by decide
@[simp] theorem hv_hvC0_ne_hvD : hvC0 ≠ hvD := by decide
@[simp] theorem hv_hvC0_ne_hvH : hvC0 ≠ hvH := by decide
@[simp] theorem hv_hvC0_ne_hvM : hvC0 ≠ hvM := by decide
@[simp] theorem hv_hvC0_ne_hvJ : hvC0 ≠ hvJ := by decide
@[simp] theorem hv_hvC0_ne_hvL : hvC0 ≠ hvL := by decide
@[simp] theorem hv_hvC0_ne_hvC1 : hvC0 ≠ hvC1 := by decide
@[simp] theorem hv_hvC0_ne_hvC2 : hvC0 ≠ hvC2 := by decide
@[simp] theorem hv_hvC0_ne_hvC3 : hvC0 ≠ hvC3 := by decide
@[simp] theorem hv_hvC0_ne_hvR : hvC0 ≠ hvR := by decide
@[simp] theorem hv_hvC0_ne_hvM2 : hvC0 ≠ hvM2 := by decide
@[simp] theorem hv_hvC0_ne_hvK1 : hvC0 ≠ hvK1 := by decide
@[simp] theorem hv_hvC0_ne_hvK2 : hvC0 ≠ hvK2 := by decide
@[simp] theorem hv_hvC0_ne_hvK3 : hvC0 ≠ hvK3 := by decide
@[simp] theorem hv_hvC0_ne_hvN : hvC0 ≠ hvN := by decide
@[simp] theorem hv_hvC0_ne_hvO : hvC0 ≠ hvO := by decide
@[simp] theorem hv_hvC0_ne_lFl : hvC0 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvC0 : lFl ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lDh : hvC0 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvC0 : lDh ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lDt : hvC0 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvC0 : lDt ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lDg : hvC0 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvC0 : lDg ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lDi : hvC0 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvC0 : lDi ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lRp : hvC0 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvC0 : lRp ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lRn : hvC0 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvC0 : lRn ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lDir : hvC0 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvC0 : lDir ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lFle : hvC0 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvC0 : lFle ≠ hvC0 := by decide
@[simp] theorem hv_hvC0_ne_lKb : hvC0 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvC0 : lKb ≠ hvC0 := by decide
@[simp] theorem hv_hvJ_ne_hvF : hvJ ≠ hvF := by decide
@[simp] theorem hv_hvJ_ne_hvW : hvJ ≠ hvW := by decide
@[simp] theorem hv_hvJ_ne_hvD : hvJ ≠ hvD := by decide
@[simp] theorem hv_hvJ_ne_hvH : hvJ ≠ hvH := by decide
@[simp] theorem hv_hvJ_ne_hvM : hvJ ≠ hvM := by decide
@[simp] theorem hv_hvJ_ne_hvC0 : hvJ ≠ hvC0 := by decide
@[simp] theorem hv_hvJ_ne_hvL : hvJ ≠ hvL := by decide
@[simp] theorem hv_hvJ_ne_hvC1 : hvJ ≠ hvC1 := by decide
@[simp] theorem hv_hvJ_ne_hvC2 : hvJ ≠ hvC2 := by decide
@[simp] theorem hv_hvJ_ne_hvC3 : hvJ ≠ hvC3 := by decide
@[simp] theorem hv_hvJ_ne_hvR : hvJ ≠ hvR := by decide
@[simp] theorem hv_hvJ_ne_hvM2 : hvJ ≠ hvM2 := by decide
@[simp] theorem hv_hvJ_ne_hvK1 : hvJ ≠ hvK1 := by decide
@[simp] theorem hv_hvJ_ne_hvK2 : hvJ ≠ hvK2 := by decide
@[simp] theorem hv_hvJ_ne_hvK3 : hvJ ≠ hvK3 := by decide
@[simp] theorem hv_hvJ_ne_hvN : hvJ ≠ hvN := by decide
@[simp] theorem hv_hvJ_ne_hvO : hvJ ≠ hvO := by decide
@[simp] theorem hv_hvJ_ne_lFl : hvJ ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvJ : lFl ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lDh : hvJ ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvJ : lDh ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lDt : hvJ ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvJ : lDt ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lDg : hvJ ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvJ : lDg ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lDi : hvJ ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvJ : lDi ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lRp : hvJ ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvJ : lRp ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lRn : hvJ ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvJ : lRn ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lDir : hvJ ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvJ : lDir ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lFle : hvJ ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvJ : lFle ≠ hvJ := by decide
@[simp] theorem hv_hvJ_ne_lKb : hvJ ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvJ : lKb ≠ hvJ := by decide
@[simp] theorem hv_hvL_ne_hvF : hvL ≠ hvF := by decide
@[simp] theorem hv_hvL_ne_hvW : hvL ≠ hvW := by decide
@[simp] theorem hv_hvL_ne_hvD : hvL ≠ hvD := by decide
@[simp] theorem hv_hvL_ne_hvH : hvL ≠ hvH := by decide
@[simp] theorem hv_hvL_ne_hvM : hvL ≠ hvM := by decide
@[simp] theorem hv_hvL_ne_hvC0 : hvL ≠ hvC0 := by decide
@[simp] theorem hv_hvL_ne_hvJ : hvL ≠ hvJ := by decide
@[simp] theorem hv_hvL_ne_hvC1 : hvL ≠ hvC1 := by decide
@[simp] theorem hv_hvL_ne_hvC2 : hvL ≠ hvC2 := by decide
@[simp] theorem hv_hvL_ne_hvC3 : hvL ≠ hvC3 := by decide
@[simp] theorem hv_hvL_ne_hvR : hvL ≠ hvR := by decide
@[simp] theorem hv_hvL_ne_hvM2 : hvL ≠ hvM2 := by decide
@[simp] theorem hv_hvL_ne_hvK1 : hvL ≠ hvK1 := by decide
@[simp] theorem hv_hvL_ne_hvK2 : hvL ≠ hvK2 := by decide
@[simp] theorem hv_hvL_ne_hvK3 : hvL ≠ hvK3 := by decide
@[simp] theorem hv_hvL_ne_hvN : hvL ≠ hvN := by decide
@[simp] theorem hv_hvL_ne_hvO : hvL ≠ hvO := by decide
@[simp] theorem hv_hvL_ne_lFl : hvL ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvL : lFl ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lDh : hvL ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvL : lDh ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lDt : hvL ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvL : lDt ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lDg : hvL ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvL : lDg ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lDi : hvL ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvL : lDi ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lRp : hvL ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvL : lRp ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lRn : hvL ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvL : lRn ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lDir : hvL ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvL : lDir ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lFle : hvL ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvL : lFle ≠ hvL := by decide
@[simp] theorem hv_hvL_ne_lKb : hvL ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvL : lKb ≠ hvL := by decide
@[simp] theorem hv_hvC1_ne_hvF : hvC1 ≠ hvF := by decide
@[simp] theorem hv_hvC1_ne_hvW : hvC1 ≠ hvW := by decide
@[simp] theorem hv_hvC1_ne_hvD : hvC1 ≠ hvD := by decide
@[simp] theorem hv_hvC1_ne_hvH : hvC1 ≠ hvH := by decide
@[simp] theorem hv_hvC1_ne_hvM : hvC1 ≠ hvM := by decide
@[simp] theorem hv_hvC1_ne_hvC0 : hvC1 ≠ hvC0 := by decide
@[simp] theorem hv_hvC1_ne_hvJ : hvC1 ≠ hvJ := by decide
@[simp] theorem hv_hvC1_ne_hvL : hvC1 ≠ hvL := by decide
@[simp] theorem hv_hvC1_ne_hvC2 : hvC1 ≠ hvC2 := by decide
@[simp] theorem hv_hvC1_ne_hvC3 : hvC1 ≠ hvC3 := by decide
@[simp] theorem hv_hvC1_ne_hvR : hvC1 ≠ hvR := by decide
@[simp] theorem hv_hvC1_ne_hvM2 : hvC1 ≠ hvM2 := by decide
@[simp] theorem hv_hvC1_ne_hvK1 : hvC1 ≠ hvK1 := by decide
@[simp] theorem hv_hvC1_ne_hvK2 : hvC1 ≠ hvK2 := by decide
@[simp] theorem hv_hvC1_ne_hvK3 : hvC1 ≠ hvK3 := by decide
@[simp] theorem hv_hvC1_ne_hvN : hvC1 ≠ hvN := by decide
@[simp] theorem hv_hvC1_ne_hvO : hvC1 ≠ hvO := by decide
@[simp] theorem hv_hvC1_ne_lFl : hvC1 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvC1 : lFl ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lDh : hvC1 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvC1 : lDh ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lDt : hvC1 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvC1 : lDt ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lDg : hvC1 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvC1 : lDg ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lDi : hvC1 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvC1 : lDi ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lRp : hvC1 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvC1 : lRp ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lRn : hvC1 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvC1 : lRn ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lDir : hvC1 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvC1 : lDir ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lFle : hvC1 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvC1 : lFle ≠ hvC1 := by decide
@[simp] theorem hv_hvC1_ne_lKb : hvC1 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvC1 : lKb ≠ hvC1 := by decide
@[simp] theorem hv_hvC2_ne_hvF : hvC2 ≠ hvF := by decide
@[simp] theorem hv_hvC2_ne_hvW : hvC2 ≠ hvW := by decide
@[simp] theorem hv_hvC2_ne_hvD : hvC2 ≠ hvD := by decide
@[simp] theorem hv_hvC2_ne_hvH : hvC2 ≠ hvH := by decide
@[simp] theorem hv_hvC2_ne_hvM : hvC2 ≠ hvM := by decide
@[simp] theorem hv_hvC2_ne_hvC0 : hvC2 ≠ hvC0 := by decide
@[simp] theorem hv_hvC2_ne_hvJ : hvC2 ≠ hvJ := by decide
@[simp] theorem hv_hvC2_ne_hvL : hvC2 ≠ hvL := by decide
@[simp] theorem hv_hvC2_ne_hvC1 : hvC2 ≠ hvC1 := by decide
@[simp] theorem hv_hvC2_ne_hvC3 : hvC2 ≠ hvC3 := by decide
@[simp] theorem hv_hvC2_ne_hvR : hvC2 ≠ hvR := by decide
@[simp] theorem hv_hvC2_ne_hvM2 : hvC2 ≠ hvM2 := by decide
@[simp] theorem hv_hvC2_ne_hvK1 : hvC2 ≠ hvK1 := by decide
@[simp] theorem hv_hvC2_ne_hvK2 : hvC2 ≠ hvK2 := by decide
@[simp] theorem hv_hvC2_ne_hvK3 : hvC2 ≠ hvK3 := by decide
@[simp] theorem hv_hvC2_ne_hvN : hvC2 ≠ hvN := by decide
@[simp] theorem hv_hvC2_ne_hvO : hvC2 ≠ hvO := by decide
@[simp] theorem hv_hvC2_ne_lFl : hvC2 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvC2 : lFl ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lDh : hvC2 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvC2 : lDh ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lDt : hvC2 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvC2 : lDt ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lDg : hvC2 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvC2 : lDg ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lDi : hvC2 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvC2 : lDi ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lRp : hvC2 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvC2 : lRp ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lRn : hvC2 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvC2 : lRn ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lDir : hvC2 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvC2 : lDir ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lFle : hvC2 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvC2 : lFle ≠ hvC2 := by decide
@[simp] theorem hv_hvC2_ne_lKb : hvC2 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvC2 : lKb ≠ hvC2 := by decide
@[simp] theorem hv_hvC3_ne_hvF : hvC3 ≠ hvF := by decide
@[simp] theorem hv_hvC3_ne_hvW : hvC3 ≠ hvW := by decide
@[simp] theorem hv_hvC3_ne_hvD : hvC3 ≠ hvD := by decide
@[simp] theorem hv_hvC3_ne_hvH : hvC3 ≠ hvH := by decide
@[simp] theorem hv_hvC3_ne_hvM : hvC3 ≠ hvM := by decide
@[simp] theorem hv_hvC3_ne_hvC0 : hvC3 ≠ hvC0 := by decide
@[simp] theorem hv_hvC3_ne_hvJ : hvC3 ≠ hvJ := by decide
@[simp] theorem hv_hvC3_ne_hvL : hvC3 ≠ hvL := by decide
@[simp] theorem hv_hvC3_ne_hvC1 : hvC3 ≠ hvC1 := by decide
@[simp] theorem hv_hvC3_ne_hvC2 : hvC3 ≠ hvC2 := by decide
@[simp] theorem hv_hvC3_ne_hvR : hvC3 ≠ hvR := by decide
@[simp] theorem hv_hvC3_ne_hvM2 : hvC3 ≠ hvM2 := by decide
@[simp] theorem hv_hvC3_ne_hvK1 : hvC3 ≠ hvK1 := by decide
@[simp] theorem hv_hvC3_ne_hvK2 : hvC3 ≠ hvK2 := by decide
@[simp] theorem hv_hvC3_ne_hvK3 : hvC3 ≠ hvK3 := by decide
@[simp] theorem hv_hvC3_ne_hvN : hvC3 ≠ hvN := by decide
@[simp] theorem hv_hvC3_ne_hvO : hvC3 ≠ hvO := by decide
@[simp] theorem hv_hvC3_ne_lFl : hvC3 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvC3 : lFl ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lDh : hvC3 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvC3 : lDh ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lDt : hvC3 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvC3 : lDt ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lDg : hvC3 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvC3 : lDg ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lDi : hvC3 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvC3 : lDi ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lRp : hvC3 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvC3 : lRp ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lRn : hvC3 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvC3 : lRn ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lDir : hvC3 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvC3 : lDir ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lFle : hvC3 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvC3 : lFle ≠ hvC3 := by decide
@[simp] theorem hv_hvC3_ne_lKb : hvC3 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvC3 : lKb ≠ hvC3 := by decide
@[simp] theorem hv_hvR_ne_hvF : hvR ≠ hvF := by decide
@[simp] theorem hv_hvR_ne_hvW : hvR ≠ hvW := by decide
@[simp] theorem hv_hvR_ne_hvD : hvR ≠ hvD := by decide
@[simp] theorem hv_hvR_ne_hvH : hvR ≠ hvH := by decide
@[simp] theorem hv_hvR_ne_hvM : hvR ≠ hvM := by decide
@[simp] theorem hv_hvR_ne_hvC0 : hvR ≠ hvC0 := by decide
@[simp] theorem hv_hvR_ne_hvJ : hvR ≠ hvJ := by decide
@[simp] theorem hv_hvR_ne_hvL : hvR ≠ hvL := by decide
@[simp] theorem hv_hvR_ne_hvC1 : hvR ≠ hvC1 := by decide
@[simp] theorem hv_hvR_ne_hvC2 : hvR ≠ hvC2 := by decide
@[simp] theorem hv_hvR_ne_hvC3 : hvR ≠ hvC3 := by decide
@[simp] theorem hv_hvR_ne_hvM2 : hvR ≠ hvM2 := by decide
@[simp] theorem hv_hvR_ne_hvK1 : hvR ≠ hvK1 := by decide
@[simp] theorem hv_hvR_ne_hvK2 : hvR ≠ hvK2 := by decide
@[simp] theorem hv_hvR_ne_hvK3 : hvR ≠ hvK3 := by decide
@[simp] theorem hv_hvR_ne_hvN : hvR ≠ hvN := by decide
@[simp] theorem hv_hvR_ne_hvO : hvR ≠ hvO := by decide
@[simp] theorem hv_hvR_ne_lFl : hvR ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvR : lFl ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lDh : hvR ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvR : lDh ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lDt : hvR ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvR : lDt ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lDg : hvR ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvR : lDg ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lDi : hvR ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvR : lDi ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lRp : hvR ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvR : lRp ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lRn : hvR ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvR : lRn ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lDir : hvR ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvR : lDir ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lFle : hvR ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvR : lFle ≠ hvR := by decide
@[simp] theorem hv_hvR_ne_lKb : hvR ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvR : lKb ≠ hvR := by decide
@[simp] theorem hv_hvM2_ne_hvF : hvM2 ≠ hvF := by decide
@[simp] theorem hv_hvM2_ne_hvW : hvM2 ≠ hvW := by decide
@[simp] theorem hv_hvM2_ne_hvD : hvM2 ≠ hvD := by decide
@[simp] theorem hv_hvM2_ne_hvH : hvM2 ≠ hvH := by decide
@[simp] theorem hv_hvM2_ne_hvM : hvM2 ≠ hvM := by decide
@[simp] theorem hv_hvM2_ne_hvC0 : hvM2 ≠ hvC0 := by decide
@[simp] theorem hv_hvM2_ne_hvJ : hvM2 ≠ hvJ := by decide
@[simp] theorem hv_hvM2_ne_hvL : hvM2 ≠ hvL := by decide
@[simp] theorem hv_hvM2_ne_hvC1 : hvM2 ≠ hvC1 := by decide
@[simp] theorem hv_hvM2_ne_hvC2 : hvM2 ≠ hvC2 := by decide
@[simp] theorem hv_hvM2_ne_hvC3 : hvM2 ≠ hvC3 := by decide
@[simp] theorem hv_hvM2_ne_hvR : hvM2 ≠ hvR := by decide
@[simp] theorem hv_hvM2_ne_hvK1 : hvM2 ≠ hvK1 := by decide
@[simp] theorem hv_hvM2_ne_hvK2 : hvM2 ≠ hvK2 := by decide
@[simp] theorem hv_hvM2_ne_hvK3 : hvM2 ≠ hvK3 := by decide
@[simp] theorem hv_hvM2_ne_hvN : hvM2 ≠ hvN := by decide
@[simp] theorem hv_hvM2_ne_hvO : hvM2 ≠ hvO := by decide
@[simp] theorem hv_hvM2_ne_lFl : hvM2 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvM2 : lFl ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lDh : hvM2 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvM2 : lDh ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lDt : hvM2 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvM2 : lDt ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lDg : hvM2 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvM2 : lDg ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lDi : hvM2 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvM2 : lDi ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lRp : hvM2 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvM2 : lRp ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lRn : hvM2 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvM2 : lRn ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lDir : hvM2 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvM2 : lDir ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lFle : hvM2 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvM2 : lFle ≠ hvM2 := by decide
@[simp] theorem hv_hvM2_ne_lKb : hvM2 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvM2 : lKb ≠ hvM2 := by decide
@[simp] theorem hv_hvK1_ne_hvF : hvK1 ≠ hvF := by decide
@[simp] theorem hv_hvK1_ne_hvW : hvK1 ≠ hvW := by decide
@[simp] theorem hv_hvK1_ne_hvD : hvK1 ≠ hvD := by decide
@[simp] theorem hv_hvK1_ne_hvH : hvK1 ≠ hvH := by decide
@[simp] theorem hv_hvK1_ne_hvM : hvK1 ≠ hvM := by decide
@[simp] theorem hv_hvK1_ne_hvC0 : hvK1 ≠ hvC0 := by decide
@[simp] theorem hv_hvK1_ne_hvJ : hvK1 ≠ hvJ := by decide
@[simp] theorem hv_hvK1_ne_hvL : hvK1 ≠ hvL := by decide
@[simp] theorem hv_hvK1_ne_hvC1 : hvK1 ≠ hvC1 := by decide
@[simp] theorem hv_hvK1_ne_hvC2 : hvK1 ≠ hvC2 := by decide
@[simp] theorem hv_hvK1_ne_hvC3 : hvK1 ≠ hvC3 := by decide
@[simp] theorem hv_hvK1_ne_hvR : hvK1 ≠ hvR := by decide
@[simp] theorem hv_hvK1_ne_hvM2 : hvK1 ≠ hvM2 := by decide
@[simp] theorem hv_hvK1_ne_hvK2 : hvK1 ≠ hvK2 := by decide
@[simp] theorem hv_hvK1_ne_hvK3 : hvK1 ≠ hvK3 := by decide
@[simp] theorem hv_hvK1_ne_hvN : hvK1 ≠ hvN := by decide
@[simp] theorem hv_hvK1_ne_hvO : hvK1 ≠ hvO := by decide
@[simp] theorem hv_hvK1_ne_lFl : hvK1 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvK1 : lFl ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lDh : hvK1 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvK1 : lDh ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lDt : hvK1 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvK1 : lDt ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lDg : hvK1 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvK1 : lDg ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lDi : hvK1 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvK1 : lDi ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lRp : hvK1 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvK1 : lRp ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lRn : hvK1 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvK1 : lRn ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lDir : hvK1 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvK1 : lDir ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lFle : hvK1 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvK1 : lFle ≠ hvK1 := by decide
@[simp] theorem hv_hvK1_ne_lKb : hvK1 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvK1 : lKb ≠ hvK1 := by decide
@[simp] theorem hv_hvK2_ne_hvF : hvK2 ≠ hvF := by decide
@[simp] theorem hv_hvK2_ne_hvW : hvK2 ≠ hvW := by decide
@[simp] theorem hv_hvK2_ne_hvD : hvK2 ≠ hvD := by decide
@[simp] theorem hv_hvK2_ne_hvH : hvK2 ≠ hvH := by decide
@[simp] theorem hv_hvK2_ne_hvM : hvK2 ≠ hvM := by decide
@[simp] theorem hv_hvK2_ne_hvC0 : hvK2 ≠ hvC0 := by decide
@[simp] theorem hv_hvK2_ne_hvJ : hvK2 ≠ hvJ := by decide
@[simp] theorem hv_hvK2_ne_hvL : hvK2 ≠ hvL := by decide
@[simp] theorem hv_hvK2_ne_hvC1 : hvK2 ≠ hvC1 := by decide
@[simp] theorem hv_hvK2_ne_hvC2 : hvK2 ≠ hvC2 := by decide
@[simp] theorem hv_hvK2_ne_hvC3 : hvK2 ≠ hvC3 := by decide
@[simp] theorem hv_hvK2_ne_hvR : hvK2 ≠ hvR := by decide
@[simp] theorem hv_hvK2_ne_hvM2 : hvK2 ≠ hvM2 := by decide
@[simp] theorem hv_hvK2_ne_hvK1 : hvK2 ≠ hvK1 := by decide
@[simp] theorem hv_hvK2_ne_hvK3 : hvK2 ≠ hvK3 := by decide
@[simp] theorem hv_hvK2_ne_hvN : hvK2 ≠ hvN := by decide
@[simp] theorem hv_hvK2_ne_hvO : hvK2 ≠ hvO := by decide
@[simp] theorem hv_hvK2_ne_lFl : hvK2 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvK2 : lFl ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lDh : hvK2 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvK2 : lDh ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lDt : hvK2 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvK2 : lDt ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lDg : hvK2 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvK2 : lDg ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lDi : hvK2 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvK2 : lDi ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lRp : hvK2 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvK2 : lRp ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lRn : hvK2 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvK2 : lRn ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lDir : hvK2 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvK2 : lDir ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lFle : hvK2 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvK2 : lFle ≠ hvK2 := by decide
@[simp] theorem hv_hvK2_ne_lKb : hvK2 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvK2 : lKb ≠ hvK2 := by decide
@[simp] theorem hv_hvK3_ne_hvF : hvK3 ≠ hvF := by decide
@[simp] theorem hv_hvK3_ne_hvW : hvK3 ≠ hvW := by decide
@[simp] theorem hv_hvK3_ne_hvD : hvK3 ≠ hvD := by decide
@[simp] theorem hv_hvK3_ne_hvH : hvK3 ≠ hvH := by decide
@[simp] theorem hv_hvK3_ne_hvM : hvK3 ≠ hvM := by decide
@[simp] theorem hv_hvK3_ne_hvC0 : hvK3 ≠ hvC0 := by decide
@[simp] theorem hv_hvK3_ne_hvJ : hvK3 ≠ hvJ := by decide
@[simp] theorem hv_hvK3_ne_hvL : hvK3 ≠ hvL := by decide
@[simp] theorem hv_hvK3_ne_hvC1 : hvK3 ≠ hvC1 := by decide
@[simp] theorem hv_hvK3_ne_hvC2 : hvK3 ≠ hvC2 := by decide
@[simp] theorem hv_hvK3_ne_hvC3 : hvK3 ≠ hvC3 := by decide
@[simp] theorem hv_hvK3_ne_hvR : hvK3 ≠ hvR := by decide
@[simp] theorem hv_hvK3_ne_hvM2 : hvK3 ≠ hvM2 := by decide
@[simp] theorem hv_hvK3_ne_hvK1 : hvK3 ≠ hvK1 := by decide
@[simp] theorem hv_hvK3_ne_hvK2 : hvK3 ≠ hvK2 := by decide
@[simp] theorem hv_hvK3_ne_hvN : hvK3 ≠ hvN := by decide
@[simp] theorem hv_hvK3_ne_hvO : hvK3 ≠ hvO := by decide
@[simp] theorem hv_hvK3_ne_lFl : hvK3 ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvK3 : lFl ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lDh : hvK3 ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvK3 : lDh ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lDt : hvK3 ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvK3 : lDt ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lDg : hvK3 ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvK3 : lDg ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lDi : hvK3 ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvK3 : lDi ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lRp : hvK3 ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvK3 : lRp ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lRn : hvK3 ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvK3 : lRn ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lDir : hvK3 ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvK3 : lDir ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lFle : hvK3 ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvK3 : lFle ≠ hvK3 := by decide
@[simp] theorem hv_hvK3_ne_lKb : hvK3 ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvK3 : lKb ≠ hvK3 := by decide
@[simp] theorem hv_hvN_ne_hvF : hvN ≠ hvF := by decide
@[simp] theorem hv_hvN_ne_hvW : hvN ≠ hvW := by decide
@[simp] theorem hv_hvN_ne_hvD : hvN ≠ hvD := by decide
@[simp] theorem hv_hvN_ne_hvH : hvN ≠ hvH := by decide
@[simp] theorem hv_hvN_ne_hvM : hvN ≠ hvM := by decide
@[simp] theorem hv_hvN_ne_hvC0 : hvN ≠ hvC0 := by decide
@[simp] theorem hv_hvN_ne_hvJ : hvN ≠ hvJ := by decide
@[simp] theorem hv_hvN_ne_hvL : hvN ≠ hvL := by decide
@[simp] theorem hv_hvN_ne_hvC1 : hvN ≠ hvC1 := by decide
@[simp] theorem hv_hvN_ne_hvC2 : hvN ≠ hvC2 := by decide
@[simp] theorem hv_hvN_ne_hvC3 : hvN ≠ hvC3 := by decide
@[simp] theorem hv_hvN_ne_hvR : hvN ≠ hvR := by decide
@[simp] theorem hv_hvN_ne_hvM2 : hvN ≠ hvM2 := by decide
@[simp] theorem hv_hvN_ne_hvK1 : hvN ≠ hvK1 := by decide
@[simp] theorem hv_hvN_ne_hvK2 : hvN ≠ hvK2 := by decide
@[simp] theorem hv_hvN_ne_hvK3 : hvN ≠ hvK3 := by decide
@[simp] theorem hv_hvN_ne_hvO : hvN ≠ hvO := by decide
@[simp] theorem hv_hvN_ne_lFl : hvN ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvN : lFl ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lDh : hvN ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvN : lDh ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lDt : hvN ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvN : lDt ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lDg : hvN ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvN : lDg ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lDi : hvN ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvN : lDi ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lRp : hvN ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvN : lRp ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lRn : hvN ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvN : lRn ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lDir : hvN ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvN : lDir ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lFle : hvN ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvN : lFle ≠ hvN := by decide
@[simp] theorem hv_hvN_ne_lKb : hvN ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvN : lKb ≠ hvN := by decide
@[simp] theorem hv_hvO_ne_hvF : hvO ≠ hvF := by decide
@[simp] theorem hv_hvO_ne_hvW : hvO ≠ hvW := by decide
@[simp] theorem hv_hvO_ne_hvD : hvO ≠ hvD := by decide
@[simp] theorem hv_hvO_ne_hvH : hvO ≠ hvH := by decide
@[simp] theorem hv_hvO_ne_hvM : hvO ≠ hvM := by decide
@[simp] theorem hv_hvO_ne_hvC0 : hvO ≠ hvC0 := by decide
@[simp] theorem hv_hvO_ne_hvJ : hvO ≠ hvJ := by decide
@[simp] theorem hv_hvO_ne_hvL : hvO ≠ hvL := by decide
@[simp] theorem hv_hvO_ne_hvC1 : hvO ≠ hvC1 := by decide
@[simp] theorem hv_hvO_ne_hvC2 : hvO ≠ hvC2 := by decide
@[simp] theorem hv_hvO_ne_hvC3 : hvO ≠ hvC3 := by decide
@[simp] theorem hv_hvO_ne_hvR : hvO ≠ hvR := by decide
@[simp] theorem hv_hvO_ne_hvM2 : hvO ≠ hvM2 := by decide
@[simp] theorem hv_hvO_ne_hvK1 : hvO ≠ hvK1 := by decide
@[simp] theorem hv_hvO_ne_hvK2 : hvO ≠ hvK2 := by decide
@[simp] theorem hv_hvO_ne_hvK3 : hvO ≠ hvK3 := by decide
@[simp] theorem hv_hvO_ne_hvN : hvO ≠ hvN := by decide
@[simp] theorem hv_hvO_ne_lFl : hvO ≠ lFl := by decide
@[simp] theorem hv_lFl_ne_hvO : lFl ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lDh : hvO ≠ lDh := by decide
@[simp] theorem hv_lDh_ne_hvO : lDh ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lDt : hvO ≠ lDt := by decide
@[simp] theorem hv_lDt_ne_hvO : lDt ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lDg : hvO ≠ lDg := by decide
@[simp] theorem hv_lDg_ne_hvO : lDg ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lDi : hvO ≠ lDi := by decide
@[simp] theorem hv_lDi_ne_hvO : lDi ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lRp : hvO ≠ lRp := by decide
@[simp] theorem hv_lRp_ne_hvO : lRp ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lRn : hvO ≠ lRn := by decide
@[simp] theorem hv_lRn_ne_hvO : lRn ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lDir : hvO ≠ lDir := by decide
@[simp] theorem hv_lDir_ne_hvO : lDir ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lFle : hvO ≠ lFle := by decide
@[simp] theorem hv_lFle_ne_hvO : lFle ≠ hvO := by decide
@[simp] theorem hv_hvO_ne_lKb : hvO ≠ lKb := by decide
@[simp] theorem hv_lKb_ne_hvO : lKb ≠ hvO := by decide

def hvParams : List MlS := [hvF, hvW, hvD, hvH, hvM]
def hvLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, hvC0, hvJ, hvL, hvC1, hvC2, hvC3, hvR, hvM2, hvK1,
  hvK2, hvK3, hvN, hvO]

def hvRet (C : Ctx) (er em : ExpHOL 64) : ProgHOL 64 :=
  allocP C hvO (.const 16) (.seq (.store (vv hvO) er) (.seq (.store (.op .add [vv hvO, .const 8]) em)
    (.return (vv hvO))))

def hvIns (C : Ctx) : ProgHOL 64 := mlInsP C hvN (vv hvH) (vv hvD) (vv hvR) (vv hvM2) (hvRet C (vv hvR) (vv hvN))

def hvCall (k : MlS) (eD eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fHv [.op .sub [vv hvF, .const 1], vv hvW, eD, eH, eM])
  (.seq (.assign .local hvR (.load .one (vv k))) (.seq (.assign .local hvM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

/-- Two children, the second at depth `eD2`; a `true` first answer short-circuits. -/
def hvArm2 (C : Ctx) (eD2 : ExpHOL 64) : ProgHOL 64 :=
  hvCall hvK1 (vv hvD) (vv hvC1) (vv hvM)
    (.ite (vv hvR) (hvIns C) (hvCall hvK2 eD2 (vv hvC2) (vv hvM2) (hvIns C)))

def hvArm3 (C : Ctx) : ProgHOL 64 :=
  hvCall hvK1 (vv hvD) (vv hvC1) (vv hvM)
    (.ite (vv hvR) (hvIns C) (hvCall hvK2 (vv hvD) (vv hvC2) (vv hvM2)
      (.ite (vv hvR) (hvIns C) (hvCall hvK3 (.op .add [vv hvD, .const 1]) (vv hvC3) (vv hvM2) (hvIns C)))))

/-- The memo probe, then the arm. -/
def hvMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, hvL), none)) fMl [vv hvM, vv hvH, vv hvD])
  (.ite (.cmp .notEqual (vv hvL) (.const 0)) (hvRet C (.op .sub [vv hvL, .const 1]) (vv hvM)) arm)

def hvBvRet (C : Ctx) : ProgHOL 64 :=
  hvRet C (.op .and [.cmp .notLower (vv hvJ) (vv hvD), .cmp .lower (.op .sub [vv hvJ, vv hvD]) (vv hvW)]) (vv hvM)

def hvBvar (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local hvJ (.const 0)) (hvBvRet C))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local hvJ (.load .one (vv lRp))) (hvBvRet C)) hang)

def hvTwo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local hvC1 (.load .one (vv lRp)))
    (.seq (.assign .local hvC2 (.load .one (.op .add [vv lRp, .const 8]))) (hvMemo C arm))

def hvCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv hvF) (.const 0)) hang
  (.seq (.call (some (some (.local, hvC0), none)) ExM.fLBB [.op .sub [vv hvF, .const 1], vv hvD, vv hvH])
  (.ite (vv hvC0) (hvRet C (.const 0) (vv hvM))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv hvH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (hvBvar C)
  (.ite (.cmp .equal (vv lDg) (.const 1)) (hvRet C (.const 0) (vv hvM))
  (.ite (.cmp .equal (vv lDg) (.const 2)) (hvRet C (.const 0) (vv hvM))
  (.ite (.cmp .equal (vv lDg) (.const 3)) (hvRet C (.const 0) (vv hvM))
  (.ite (.cmp .equal (vv lDg) (.const 8)) (hvRet C (.const 0) (vv hvM))
  (.ite (.cmp .equal (vv lDg) (.const 4)) (hvTwo C (hvArm2 C (vv hvD)))
  (.ite (.cmp .equal (vv lDg) (.const 5)) (hvTwo C (hvArm2 C (.op .add [vv hvD, .const 1])))
  (.ite (.cmp .equal (vv lDg) (.const 6)) (hvTwo C (hvArm2 C (.op .add [vv hvD, .const 1])))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local hvC1 (.load .one (vv lRp)))
      (.seq (.assign .local hvC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local hvC3 (.load .one (.op .add [vv lRp, .const 16]))) (hvMemo C (hvArm3 C)))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local hvC1 (.load .one (.op .add [vv lRp, .const 8])))
      (hvMemo C (hvCall hvK1 (vv hvD) (vv hvC1) (vv hvM) (hvIns C))))
    hang)))))))))))))))

def hvBody (C : Ctx) : ProgHOL 64 := prologue hvLocals (hvCore C)

structure HvCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  lbb : C.code.lookup ExM.fLBB = some ([(pFu, .one), (ExM.pKb, .one), (pH, .one)], ExM.lbbBody, .one)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  cB : ExB.CodesB C (ExB.bodyB C)
  self : C.code.lookup fHv = some (hvParams.map (fun p => (p, ShapeHOL.one)), hvBody C, .one)

section
variable {σ : Type}

/-- The answer and memo as a fresh pair block. -/
def PostHv (C : Ctx) (rm : Bool × Std.HashMap (EIdx × Nat) Bool) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H' o pm, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm ∧
    WsRep C H' pm rm.2 ∧ SR (ctxH C H') s' st

theorem postHv_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostHv C a w s' st → PostHv C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, pm, h2, h3, h4, h5, h6, h7⟩ => ⟨H', o, pm, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem specR_hvRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hD : hvO ∈ D) (her : ∀ w, sev ((hvO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((hvO, w) :: Γ) em = some pm)
    (hrep : WsRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (hvRet C er em) s (pure (r, memo)) (PostHv (ctxH C H0)) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) hvO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((hvO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv hvO) er H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (boolW r) (by simp <;> rfl) (her _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (boolW r))) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv hvO, .const 8]) em (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) pm (by simp +decide [sev]; exact cellA_add8 C _) (hem _) ?_
  have g0 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length]? = some (boolW r) := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length + 1]? = some pm := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨_, H1.length, pm, h0.trans hpre, rfl, g0, g1, wsRep_toH (wsRep_mono hpre hrep),
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_hvInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap (EIdx × Nat) Bool) (hD : hvN ∈ D ∧ hvO ∈ D) (hH : Γ.get hvH = some (Enc.idxW h))
    (hDv : Γ.get hvD = some (BitVec.ofNat 64 d)) (hR : Γ.get hvR = some (boolW r)) (hM : Γ.get hvM2 = some pm)
    (hrep : WsRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (hvIns C) s (pure (r, memo.insert (h, d) r)) (PostHv (ctxH C H0)) := by
  obtain ⟨xs, hm, he⟩ := hrep
  unfold hvIns
  refine specR_mlInsI hok hvN (vv hvH) (vv hvD) (vv hvR) (vv hvM2) (Enc.idxW h) (BitVec.ofNat 64 d) pm r xs hD.1
    (fun w => by simp [Env.get, hH]) (fun w => by simp [Env.get, hDv]) (fun w => by simp [Env.get, hR])
    (fun w => by simp [Env.get, hM]) hm (fun H' o hp' hm' => ?_)
  exact specR_hvRetI hok (vv hvR) (vv hvN) r (cellA C o) (memo.insert (h, d) r) hD.2
    (fun w => by simp [Env.get, hR]) (fun w => by simp [Env.get]) (wsRep_insert (p := pm) he h d hd r hm') (h0.trans hp')

theorem hv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ hvLocals → (ctxEnv C ++ hvParams.zip vals).get x = none :=
  Knot.params_none C hvLocals hvParams vals (by decide) (by decide)

/-- The walk's spec at fuel `n` (window `w` fixed), for every argument. -/
def HvRec (C : Ctx) (msg : String) (w n : Nat) : Prop :=
  ∀ (d : Nat) (h : EIdx) (memo : Std.HashMap (EIdx × Nat) Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → d + n < 2 ^ 63 → WsRep C H pm memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (hvParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 w, BitVec.ofNat 64 d,
      Enc.idxW h, pm])) (hvBody C) s (hlGo msg memo w d n h) (PostHv (ctxH C H))

theorem specR_hvCallI {α : Type} {C : Ctx} (hok : CtxOK C) (hc : HvCodes C) {msg : String} {w n : Nat} (ih : HvRec (σ := σ) C msg w n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap (EIdx × Nat) Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eD eH eM : ExpHOL 64) (d : Nat) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hx : x ∈ D ∧ hvR ∈ D ∧ hvM2 ∈ D) (hxn : x ≠ hvR ∧ hvM2 ≠ x) (hp : C.H <+: H) (hd : d + n < 2 ^ 63)
    (hrep : WsRep C H pm memo)
    (hF : Γ.get hvF = some (BitVec.ofNat 64 (n + 1))) (hW : Γ.get hvW = some (BitVec.ofNat 64 w))
    (heD : sev Γ eD = some (BitVec.ofNat 64 d)) (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap (EIdx × Nat) Bool) H' pm' wv s', H <+: H' → WsRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s' ((hvM2, pm') :: (hvR, boolW rm.1) :: (x, wv) :: Γ) [] D) rest s' (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (hvCall x eD eH eM rest) s (hlGo msg memo w d n h >>= k) R := by
  unfold hvCall
  refine specR_callNIH (C := ctxH C H) x fHv hvParams [.op .sub [vv hvF, .const 1], vv hvW, eD, eH, eM] (hvBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 w, BitVec.ofNat 64 d, Enc.idxW h, pm] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, by simp [hW], heD, heH, heM, trivial⟩
    (PostHv (ctxH C H))
    (fun rm wv s' H' => ∃ o pm', wv = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      WsRep C H' pm' rm.2)
    (fun rm wv s' st ⟨H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨o, pm', hw, h0, h1', wsRep_ofH hrep'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hvParams _ rfl hlk) (ih d h memo H s pm hp hd hrep))
    (fun rm wv s' H' hp' ⟨o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H') hvR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') hvM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) s' hp' hrep'

theorem codesB_H {C : Ctx} (hc : ExB.CodesB C (ExB.bodyB C)) (H : List (BitVec 64)) :
    ExB.CodesB (ctxH C H) (ExB.bodyB (ctxH C H)) :=
  ⟨hc.bvr, hc.memoGet, hc.memoProbe, hc.memoSet, hc.memoIns⟩

theorem bvarB_cut {β : Type} (fuel d : Nat) (h : EIdx) (A B : AM β) :
    (bvarB fuel h >>= fun bb => if bb ≤ d then A else B) =
      (looseBVarsBoundedFast fuel d h >>= fun c => if c = true then A else B) := by
  simp [looseBVarsBoundedFast, bind_assoc]

theorem specR_hvArm2I {C : Ctx} (hok : CtxOK C) (hc : HvCodes C) {msg : String} {w n : Nat} (ih : HvRec (σ := σ) C msg w n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (eD2 : ExpHOL 64) (h : EIdx) (d d2 : Nat)
    (hd : d + (n + 1) < 2 ^ 63) (hd2 : d2 ≤ d + 1)
    (c1 c2 : EIdx) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hD : hvK1 ∈ D ∧ hvK2 ∈ D ∧ hvR ∈ D ∧ hvM2 ∈ D ∧ hvN ∈ D ∧ hvO ∈ D) (hp : C.H <+: H) (h0 : H0 <+: H)
    (hrep : WsRep C H pm memo) (hF : Γ.get hvF = some (BitVec.ofNat 64 (n + 1)))
    (hW : Γ.get hvW = some (BitVec.ofNat 64 w))
    (hDv : Γ.get hvD = some (BitVec.ofNat 64 d)) (hH : Γ.get hvH = some (Enc.idxW h)) (hM : Γ.get hvM = some pm)
    (hC1 : Γ.get hvC1 = some (Enc.idxW c1)) (hC2 : Γ.get hvC2 = some (Enc.idxW c2))
    (hE2 : ∀ Γ' : Env, Γ'.get hvD = some (BitVec.ofNat 64 d) → sev Γ' eD2 = some (BitVec.ofNat 64 d2)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (hvArm2 C eD2) s
      (hlGo msg memo w d n c1 >>= fun x => match x with
        | (true, memo) => pure (true, memo) >>= fun y => pure (hasLooseBVarBIns h d y)
        | (false, memo) => hlGo msg memo w d2 n c2 >>= fun y => pure (hasLooseBVarBIns h d y))
      (PostHv (ctxH C H0)) := by
  unfold hvArm2
  refine specR_hvCallI hok hc ih hvK1 (vv hvD) (vv hvC1) (vv hvM) d c1 pm memo ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp (by omega) hrep hF hW (by simp [hDv]) (by simp [hC1]) (by simp [hM])
    (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  obtain ⟨rf, m1⟩ := rm
  cases rf
  · refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    refine specR_hvCallI hok hc ih hvK2 eD2 (vv hvC2) (vv hvM2) d2 c2 pm1 m1 ⟨hD.2.1, hD.2.2.1, hD.2.2.2.1⟩
      ⟨by decide, by decide⟩ (hp.trans hp1) (by omega) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hW])
      (hE2 _ (by simp [Env.get, hDv])) (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 s2 hp2 hrep2 => ?_)
    obtain ⟨r2, m2⟩ := rm
    simp only [hasLooseBVarBIns]
    exact specR_hvInsI hok h d (by omega) r2 pm2 m2 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep2 (h0.trans (hp1.trans hp2))
  · refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    simp only [pure_bind, hasLooseBVarBIns]
    exact specR_hvInsI hok h d (by omega) true pm1 m1 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep1 (h0.trans hp1)

theorem specR_hvArm3I {C : Ctx} (hok : CtxOK C) (hc : HvCodes C) {msg : String} {w n : Nat} (ih : HvRec (σ := σ) C msg w n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx) (d : Nat)
    (hd : d + (n + 1) < 2 ^ 63) (c1 c2 c3 : EIdx) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hD : hvK1 ∈ D ∧ hvK2 ∈ D ∧ hvK3 ∈ D ∧ hvR ∈ D ∧ hvM2 ∈ D ∧ hvN ∈ D ∧ hvO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : WsRep C H pm memo) (hF : Γ.get hvF = some (BitVec.ofNat 64 (n + 1)))
    (hW : Γ.get hvW = some (BitVec.ofNat 64 w))
    (hDv : Γ.get hvD = some (BitVec.ofNat 64 d)) (hH : Γ.get hvH = some (Enc.idxW h)) (hM : Γ.get hvM = some pm)
    (hC1 : Γ.get hvC1 = some (Enc.idxW c1)) (hC2 : Γ.get hvC2 = some (Enc.idxW c2))
    (hC3 : Γ.get hvC3 = some (Enc.idxW c3)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (hvArm3 C) s
      (hlGo msg memo w d n c1 >>= fun x => match x with
        | (true, memo) => pure (true, memo) >>= fun y => pure (hasLooseBVarBIns h d y)
        | (false, memo) => hlGo msg memo w d n c2 >>= fun z => match z with
          | (true, memo) => pure (true, memo) >>= fun y => pure (hasLooseBVarBIns h d y)
          | (false, memo) => hlGo msg memo w (d + 1) n c3 >>= fun y => pure (hasLooseBVarBIns h d y))
      (PostHv (ctxH C H0)) := by
  unfold hvArm3
  refine specR_hvCallI hok hc ih hvK1 (vv hvD) (vv hvC1) (vv hvM) d c1 pm memo ⟨hD.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp (by omega) hrep hF hW (by simp [hDv]) (by simp [hC1]) (by simp [hM])
    (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  obtain ⟨rt, m1⟩ := rm
  cases rt
  swap
  · refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    simp only [pure_bind, hasLooseBVarBIns]
    exact specR_hvInsI hok h d (by omega) true pm1 m1 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep1 (h0.trans hp1)
  refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_hvCallI hok hc ih hvK2 (vv hvD) (vv hvC2) (vv hvM2) d c2 pm1 m1 ⟨hD.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) (by omega) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hW])
    (by simp [Env.get, hDv]) (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 s2 hp2 hrep2 => ?_)
  obtain ⟨rv, m2⟩ := rm
  cases rv
  swap
  · refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    simp only [pure_bind, hasLooseBVarBIns]
    exact specR_hvInsI hok h d (by omega) true pm2 m2 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep2 (h0.trans (hp1.trans hp2))
  refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_hvCallI hok hc ih hvK3 (.op .add [vv hvD, .const 1]) (vv hvC3) (vv hvM2) (d + 1) c3 pm2 m2
    ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩ ⟨by decide, by decide⟩ ((hp.trans hp1).trans hp2) (by omega) hrep2
    (by simp [Env.get, hF]) (by simp [Env.get, hW])
    (by simp [sev, Env.get, hDv]; exact word_add1_eq d) (by simp [Env.get, hC3]) (by simp [Env.get])
    (fun rm H3 pm3 w3 s3 hp3 hrep3 => ?_)
  obtain ⟨r3, m3⟩ := rm
  simp only [hasLooseBVarBIns]
  exact specR_hvInsI hok h d (by omega) r3 pm3 m3 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
    (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep3 (h0.trans (hp1.trans (hp2.trans hp3)))

/-- The memo probe: a hit answers, a miss runs the arm. -/
theorem specR_hvMemoI {C : Ctx} (hok : CtxOK C) (hc : HvCodes C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {arm : ProgHOL 64} {k : AM (Bool × Std.HashMap (EIdx × Nat) Bool)} (h : EIdx) (d : Nat)
    (hd : d < 2 ^ 63) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool) (hD : hvL ∈ D ∧ hvO ∈ D)
    (hH : Γ.get hvH = some (Enc.idxW h)) (hDv : Γ.get hvD = some (BitVec.ofNat 64 d)) (hM : Γ.get hvM = some pm)
    (hrep : WsRep C H pm memo) (h0 : H0 <+: H)
    (hArm : SpecR (σ := σ) (Inv (ctxH C H) s ((hvL, 0) :: Γ) [] D) arm s k (PostHv (ctxH C H0))) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (hvMemo C arm) s
      (match memo[(h, d)]? with | some r => pure (r, memo) | none => k) (PostHv (ctxH C H0)) := by
  obtain ⟨xs, hm, he⟩ := id hrep
  unfold hvMemo
  refine specR_callPure (C := ctxH C H) hvL fMl mlParams [vv hvM, vv hvH, vv hvD] mlBody
    [pm, Enc.idxW h, BitVec.ofNat 64 d] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 d)) (by decide) rfl hD.1 hc.ml
    ⟨by simp [hM], by simp [hH], by simp [hDv], trivial⟩
    (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
    (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 d) xs pm H s (mnodes_toH hm)))
    (fun w H' _ ⟨hw, hH'⟩ => ?_)
  subst hw; subst H'
  rw [he h d hd]
  cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 d) with
  | some r =>
    have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_hvRetI hok _ (vv hvM) r pm memo hD.2
      (fun w => by simp [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun w => by simp [Env.get, hM]) hrep h0
  | none =>
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    exact hArm

theorem hv_bv_eval (i d w : Nat) (hi : i < 2 ^ 64) (hd : d < 2 ^ 64) (hw : w < 2 ^ 64) :
    ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 i) (BitVec.ofNat 64 d) then 1 else 0) &&&
      (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i - BitVec.ofNat 64 d)
        (BitVec.ofNat 64 w) then 1 else 0) : BitVec 64) = boolW (decide (d ≤ i) && decide (i - d < w)) := by
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_sub,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hw]
  by_cases h1 : d ≤ i
  · have e : (2 ^ 64 - d + i) % 2 ^ 64 = i - d := by
      rw [show 2 ^ 64 - d + i = (i - d) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    by_cases h2 : i - d < w
    · simp [h1, h2, boolW, show ¬ i < d by omega]
    · simp [h1, h2, boolW, show ¬ i < d by omega]
  · simp [h1, boolW, show i < d by omega]

theorem hv_spec (C : Ctx) (hok : CtxOK C) (hc : HvCodes C) (msg : String) (w : Nat) (hw : w < 2 ^ 64) :
    ∀ n, n < 2 ^ 64 → HvRec (σ := σ) C msg w n := by
  intro n
  induction n with
  | zero =>
    intro _ d h memo H s pm hp hd hrep
    refine specR_prologue (postHv_locals _) (hv_none _ _) ?_
    unfold hvCore
    rw [hlGo]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, hvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn d h memo H s pm hp hd hrep
  have ih' := ih (by omega)
  refine specR_prologue (postHv_locals _) (hv_none _ _) ?_
  unfold hvCore
  rw [hlGo]
  have hne := ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, hvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  rw [bvarB_cut]
  refine specR_callNIM (C := ctxH C H) hvC0 ExM.fLBB [pFu, ExM.pKb, pH] [.op .sub [vv hvF, .const 1], vv hvD, vv hvH]
    ExM.lbbBody [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h] (by decide) rfl (by decide) hc.lbb
    ⟨by simp +decide [sev, Env.get, hvParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, hvParams, ctxEnv], by simp +decide [Env.get, hvParams, ctxEnv], trivial⟩
    (ExM.PostB (ctxH C H)) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
      (ExM.lbb_spec (ctxH C H) (ctxOK_H hok H) (codesB_H hc.cB H) hc.bvb s n d h (by omega) (by omega)))
    (fun c wv s1 st ⟨hwv, _⟩ => ?_)
  subst hwv
  cases c
  swap
  · refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_hvRetI hok (.const 0) (vv hvM) false pm memo (by decide) (fun w => by simp [sev, boolW])
      (fun w => by simp +decide [Env.get, hvParams, ctxEnv]) hrep (List.prefix_refl _)
  refine specR_ifI _ 0 (by simp) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv hvH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, hvParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq h v _ s1 hv) ?_
  rcases v with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨pn, pi, sub⟩
  · -- bvar
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    unfold hvBvar
    have hlen : (encEView (.bvar i)).length = (Enc.limbs i).length := by simp [encEView, Enc.encBVar]
    have hfin : ∀ (Γ' : Env) (M' : Mem), i < 2 ^ 64 → Γ'.get hvJ = some (BitVec.ofNat 64 i) →
        Γ'.get hvD = some (BitVec.ofNat 64 d) → Γ'.get hvW = some (BitVec.ofNat 64 w) → Γ'.get hvM = some pm →
        SpecR (σ := σ) (Inv (ctxH C H) s1 Γ' M' (ctxLocals ++ hvLocals)) (hvBvRet C) s1
          (pure (decide (d ≤ i) && decide (i - d < w), memo)) (PostHv (ctxH C H)) := by
      intro Γ' M' hi hJ hDv hW hM
      exact specR_hvRetI hok _ (vv hvM) _ pm memo (by decide)
        (fun w' => by simp [sev, Env.get, hJ, hDv, hW]; exact hv_bv_eval i d w hi (by omega) hw)
        (fun w' => by simp [Env.get, hM]) hrep (List.prefix_refl _)
    by_cases i0 : i = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI hvJ (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      refine hfin _ _ (by decide) ?_ ?_ ?_ ?_ <;> simp +decide [Env.get, hvParams, ctxEnv]
    · by_cases ib : i < 2 ^ 64
      · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' hvJ (vv lRp) P (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by decide) (by simp) (by simp)
          (by simpa [encEView, Enc.encBVar, hl] using wordsAt_mem0 P (BitVec.ofNat 64 i) [] []) ?_
        refine hfin _ _ ib ?_ ?_ ?_ ?_ <;> simp +decide [Env.get, hvParams, ctxEnv]
      · have hl := ExI.limbs_len_ge2 i (by omega)
        have hlt : (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  · -- fvar
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    exact specR_hvRetI hok (.const 0) (vv hvM) false pm memo (by decide) (fun w => by simp [sev, boolW])
      (fun w => by simp +decide [Env.get, hvParams, ctxEnv]) hrep (List.prefix_refl _)
  · -- sort
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    exact specR_hvRetI hok (.const 0) (vv hvM) false pm memo (by decide) (fun w => by simp [sev, boolW])
      (fun w => by simp +decide [Env.get, hvParams, ctxEnv]) hrep (List.prefix_refl _)
  · -- const
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    exact specR_hvRetI hok (.const 0) (vv hvM) false pm memo (by decide) (fun w => by simp [sev, boolW])
      (fun w => by simp +decide [Env.get, hvParams, ctxEnv]) hrep (List.prefix_refl _)
  · -- app
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    unfold hvTwo
    refine specR_loadI' hvC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' hvC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P _ _ [] []) ?_
    refine specR_hvMemoI hok hc h d (by omega) pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) hrep
      (List.prefix_refl _) ?_
    exact specR_hvArm2I hok hc ih' (vv hvD) h d d (by omega) (by omega) f a pm memo
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep (by simp +decide [Env.get, hvParams, ctxEnv])
      (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (fun Γ' h' => by simp [h'])
  · -- lam
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    unfold hvTwo
    refine specR_loadI' hvC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' hvC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    refine specR_hvMemoI hok hc h d (by omega) pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) hrep
      (List.prefix_refl _) ?_
    exact specR_hvArm2I hok hc ih' (.op .add [vv hvD, .const 1]) h d (d + 1) (by omega) (by omega) ty b pm memo
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep (by simp +decide [Env.get, hvParams, ctxEnv])
      (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (fun Γ' h' => by simp [sev, h']; exact word_add1_eq d)
  · -- forallE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    unfold hvTwo
    refine specR_loadI' hvC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' hvC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    refine specR_hvMemoI hok hc h d (by omega) pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) hrep
      (List.prefix_refl _) ?_
    exact specR_hvArm2I hok hc ih' (.op .add [vv hvD, .const 1]) h d (d + 1) (by omega) (by omega) ty b pm memo
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep (by simp +decide [Env.get, hvParams, ctxEnv])
      (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (fun Γ' h' => by simp [sev, h']; exact word_add1_eq d)
  · -- letE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    refine specR_loadI' hvC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' hvC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P _ _ [Enc.idxW b] []) ?_
    refine specR_loadI' hvC3 _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using (wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) [] :
        (P + BitVec.ofNat 64 (8 * 2), Enc.idxW b) ∈ _)) ?_
    refine specR_hvMemoI hok hc h d (by omega) pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) hrep
      (List.prefix_refl _) ?_
    exact specR_hvArm3I hok hc ih' h d (by omega) ty v b pm memo
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep
      (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv])
  · -- lit
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    exact specR_hvRetI hok (.const 0) (vv hvM) false pm memo (by decide) (fun w => by simp [sev, boolW])
      (fun w => by simp +decide [Env.get, hvParams, ctxEnv]) hrep (List.prefix_refl _)
  · -- proj
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    refine specR_loadI' hvC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW pn) (Enc.idxW sub) (Enc.limbs pi) []) ?_
    refine specR_hvMemoI hok hc h d (by omega) pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) hrep
      (List.prefix_refl _) ?_
    refine specR_hvCallI hok hc ih' hvK1 (vv hvD) (vv hvC1) (vv hvM) d sub pm memo ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide⟩ hp (by omega) hrep (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv])
      (fun rm H1 pm1 w1 s2 hp1 hrep1 => ?_)
    obtain ⟨r1, m1⟩ := rm
    simp only [hasLooseBVarBIns]
    exact specR_hvInsI hok h d (by omega) r1 pm1 m1 ⟨by decide, by decide⟩ (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp +decide [Env.get, hvParams, ctxEnv]) (by simp [Env.get])
      (by simp [Env.get]) hrep1 hp1

end

/-! ## The wrappers: `hasLooseBVarIn`, and `hasLooseBVarBFast` as its window-`1` case -/

theorem hlIn_eq : ∀ fuel (memo : Std.HashMap (EIdx × Nat) Bool) (w d : Nat) (h : EIdx),
    hasLooseBVarInGo memo w d fuel h = hlGo "fuel exhausted: hasLooseBVarIn" memo w d fuel h := by
  intro fuel
  induction fuel with
  | zero => intro memo w d h; rw [hasLooseBVarInGo, hlGo]
  | succ n ih =>
    intro memo w d h
    rw [hasLooseBVarInGo, hlGo]
    simp only [ih]
    rfl

theorem hlB_eq : ∀ fuel (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (h : EIdx),
    hasLooseBVarBGo memo i fuel h = hlGo "fuel exhausted: hasLooseBVarB" memo 1 i fuel h := by
  intro fuel
  induction fuel with
  | zero => intro memo i h; rw [hasLooseBVarBGo, hlGo]
  | succ n ih =>
    intro memo i h
    rw [hasLooseBVarBGo, hlGo]
    have hb : ∀ j : Nat, (i == j) = (decide (i ≤ j) && decide (j - i < 1)) := by
      intro j
      by_cases hij : i = j
      · subst hij; simp
      · rw [show (i == j) = false by simpa using hij]
        symm
        rw [Bool.and_eq_false_iff]
        by_cases h2 : i ≤ j
        · right; simp; omega
        · left; simp; omega
    congr 1; funext bb
    split
    · rfl
    · congr 1; funext v
      cases v <;> (try simp only [ih, hb]) <;> rfl

def hiD := ofString "hin_d"
def hiW := ofString "hin_w"
def hiE := ofString "hin_e"
def hiK := ofString "hin_k"
def hiR := ofString "hin_r"
def fHi := ofString "hasLooseBVarIn"

def hiParams : List MlS := [hiD, hiW, hiE]
def hiLocals : List MlS := [hiK, hiR]

def hiBody : ProgHOL 64 := prologue hiLocals
  (.ite (.cmp .equal (vv hiW) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, hiK), none)) fHv
      [.const (BitVec.ofNat 64 coreWalkFuel), vv hiW, vv hiD, vv hiE, .const 0])
  (.seq (.assign .local hiR (.load .one (vv hiK))) (.return (vv hiR)))))

section
variable {σ : Type}

theorem hi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ hiLocals → (ctxEnv C ++ hiParams.zip vals).get x = none :=
  Knot.params_none C hiLocals hiParams vals (by decide) (by decide)

theorem hi_specG (C : Ctx) (hok : CtxOK C) (hc : HvCodes C) (msg : String) (s : AState) (d w : Nat) (e : EIdx)
    (hd : d + coreWalkFuel < 2 ^ 63) (hw : w < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (hiParams.zip [BitVec.ofNat 64 d, BitVec.ofNat 64 w, Enc.idxW e])) hiBody s
      (if w == 0 then pure false else do pure (← hlGo msg ∅ w d coreWalkFuel e).1) (PostB C) := by
  refine specR_prologue (postB_locals C) (hi_none C _) ?_
  by_cases w0 : w = 0
  · subst w0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, hiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : BitVec.ofNat 64 w ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, hiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (w == 0) = false by simpa using w0, Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := C) hiK fHv hvParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv hiW, vv hiD, vv hiE, .const 0] (hvBody C)
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 w, BitVec.ofNat 64 d, Enc.idxW e, 0] (by decide) rfl (by decide)
    hc.self ⟨rfl, by simp +decide [Env.get, hiParams, ctxEnv], by simp +decide [Env.get, hiParams, ctxEnv],
      by simp +decide [Env.get, hiParams, ctxEnv], rfl, trivial⟩
    (PostHv C)
    (fun rm wv s' H' => ∃ o, wv = cellA C o ∧ H'[o]? = some (boolW rm.1))
    (fun rm wv s' st ⟨H', o, pm', hp', hwv, h0, _, _, hsr⟩ => ⟨H', hp', ⟨o, hwv, h0⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hvParams _ rfl hlk)
      (hv_spec C hok hc msg w hw coreWalkFuel CV.coreWalkFuel_lt d e ∅ C.H s 0 (List.prefix_refl _) hd
        (wsRep_empty C C.H)))
    (fun rm wv s1 H1 hp1 ⟨o, hwv, h0⟩ => ?_)
  subst hwv
  refine UD.specR_heapLoadI' (C := ctxH C H1) hiR (vv hiK) o (boolW rm.1) h0 (by decide) (by simp; rfl) ?_
  exact specR_returnI _ (boolW rm.1) (by simp)
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem hi_spec (C : Ctx) (hok : CtxOK C) (hc : HvCodes C) (s : AState) (d w : Nat) (e : EIdx)
    (hd : d + coreWalkFuel < 2 ^ 63) (hw : w < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (hiParams.zip [BitVec.ofNat 64 d, BitVec.ofNat 64 w, Enc.idxW e])) hiBody s
      (hasLooseBVarIn d w e) (PostB C) := by
  have := hi_specG (σ := σ) C hok hc "fuel exhausted: hasLooseBVarIn" s d w e hd hw
  simpa [hasLooseBVarIn, hlIn_eq] using this

theorem hb_spec (C : Ctx) (hok : CtxOK C) (hc : HvCodes C) (s : AState) (i : Nat) (e : EIdx)
    (hd : i + coreWalkFuel < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (hiParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 1, Enc.idxW e])) hiBody s
      (hasLooseBVarBFast i e) (PostB C) := by
  have := hi_specG (σ := σ) C hok hc "fuel exhausted: hasLooseBVarB" s i 1 e hd (by norm_num)
  simpa [hasLooseBVarBFast, hlB_eq] using this
end

end ConPanqueque.T.WC
