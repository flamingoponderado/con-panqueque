import ConPanqueque.T.Core.ZeParam
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `zeS` over a level handle: the zero-ness parameter list empty after a parameter substitution

As `ze`, except that a `param` node is looked up among the parameter names and its argument walked (`nzParam`).
-/

namespace ConPanqueque.T.WC

/-- `ze` after a parameter substitution, looking parameters up. -/
def zeS (ks : List ConLeche.Name) (vs : List ConLeche.Level) : ConLeche.Level → Bool
  | .zero => true
  | .succ _ => true
  | .param n => ze (ConLeche.Level.subst.go ks vs n)
  | .max a b => zeS ks vs a && zeS ks vs b
  | .imax _ b => zeS ks vs b

theorem ze_subst (ks : List ConLeche.Name) (vs : List ConLeche.Level) : ∀ l, ze (ConLeche.Level.subst ks vs l) = zeS ks vs l
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .max a b => by simp only [ConLeche.Level.subst, ze, zeS, ze_subst ks vs a, ze_subst ks vs b]
  | .imax a b => by simp only [ConLeche.Level.subst, ze, zeS, ze_subst ks vs b]

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def zvU := ofString "zvu"
def zvK := ofString "zvk"
def zvL := ofString "zvl"
def zvUs := ofString "zvus"
def zvA := ofString "zva"
def zvB := ofString "zvb"
def zvX := ofString "zvx"
def zvY := ofString "zvy"
def zvN := ofString "zvn"
def fZv := ofString "zpsEmptySubst"

@[simp] theorem zv_zsU_ne_zsK : zvU ≠ zvK := by decide
@[simp] theorem zv_zsU_ne_zsL : zvU ≠ zvL := by decide
@[simp] theorem zv_zsU_ne_zsUs : zvU ≠ zvUs := by decide
@[simp] theorem zv_zsU_ne_zsA : zvU ≠ zvA := by decide
@[simp] theorem zv_zsU_ne_zsB : zvU ≠ zvB := by decide
@[simp] theorem zv_zsU_ne_zsX : zvU ≠ zvX := by decide
@[simp] theorem zv_zsU_ne_zsY : zvU ≠ zvY := by decide
@[simp] theorem zv_zsU_ne_zsN : zvU ≠ zvN := by decide
@[simp] theorem zv_zsU_ne_lFl : zvU ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsU : lFl ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lDh : zvU ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsU : lDh ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lDt : zvU ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsU : lDt ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lDg : zvU ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsU : lDg ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lDi : zvU ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsU : lDi ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lRp : zvU ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsU : lRp ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lRn : zvU ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsU : lRn ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lFll : zvU ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsU : lFll ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lDir : zvU ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsU : lDir ≠ zvU := by decide
@[simp] theorem zv_zsU_ne_lKb : zvU ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsU : lKb ≠ zvU := by decide
@[simp] theorem zv_zsK_ne_zsU : zvK ≠ zvU := by decide
@[simp] theorem zv_zsK_ne_zsL : zvK ≠ zvL := by decide
@[simp] theorem zv_zsK_ne_zsUs : zvK ≠ zvUs := by decide
@[simp] theorem zv_zsK_ne_zsA : zvK ≠ zvA := by decide
@[simp] theorem zv_zsK_ne_zsB : zvK ≠ zvB := by decide
@[simp] theorem zv_zsK_ne_zsX : zvK ≠ zvX := by decide
@[simp] theorem zv_zsK_ne_zsY : zvK ≠ zvY := by decide
@[simp] theorem zv_zsK_ne_zsN : zvK ≠ zvN := by decide
@[simp] theorem zv_zsK_ne_lFl : zvK ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsK : lFl ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lDh : zvK ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsK : lDh ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lDt : zvK ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsK : lDt ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lDg : zvK ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsK : lDg ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lDi : zvK ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsK : lDi ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lRp : zvK ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsK : lRp ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lRn : zvK ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsK : lRn ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lFll : zvK ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsK : lFll ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lDir : zvK ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsK : lDir ≠ zvK := by decide
@[simp] theorem zv_zsK_ne_lKb : zvK ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsK : lKb ≠ zvK := by decide
@[simp] theorem zv_zsL_ne_zsU : zvL ≠ zvU := by decide
@[simp] theorem zv_zsL_ne_zsK : zvL ≠ zvK := by decide
@[simp] theorem zv_zsL_ne_zsUs : zvL ≠ zvUs := by decide
@[simp] theorem zv_zsL_ne_zsA : zvL ≠ zvA := by decide
@[simp] theorem zv_zsL_ne_zsB : zvL ≠ zvB := by decide
@[simp] theorem zv_zsL_ne_zsX : zvL ≠ zvX := by decide
@[simp] theorem zv_zsL_ne_zsY : zvL ≠ zvY := by decide
@[simp] theorem zv_zsL_ne_zsN : zvL ≠ zvN := by decide
@[simp] theorem zv_zsL_ne_lFl : zvL ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsL : lFl ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lDh : zvL ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsL : lDh ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lDt : zvL ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsL : lDt ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lDg : zvL ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsL : lDg ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lDi : zvL ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsL : lDi ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lRp : zvL ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsL : lRp ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lRn : zvL ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsL : lRn ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lFll : zvL ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsL : lFll ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lDir : zvL ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsL : lDir ≠ zvL := by decide
@[simp] theorem zv_zsL_ne_lKb : zvL ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsL : lKb ≠ zvL := by decide
@[simp] theorem zv_zsUs_ne_zsU : zvUs ≠ zvU := by decide
@[simp] theorem zv_zsUs_ne_zsK : zvUs ≠ zvK := by decide
@[simp] theorem zv_zsUs_ne_zsL : zvUs ≠ zvL := by decide
@[simp] theorem zv_zsUs_ne_zsA : zvUs ≠ zvA := by decide
@[simp] theorem zv_zsUs_ne_zsB : zvUs ≠ zvB := by decide
@[simp] theorem zv_zsUs_ne_zsX : zvUs ≠ zvX := by decide
@[simp] theorem zv_zsUs_ne_zsY : zvUs ≠ zvY := by decide
@[simp] theorem zv_zsUs_ne_zsN : zvUs ≠ zvN := by decide
@[simp] theorem zv_zsUs_ne_lFl : zvUs ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsUs : lFl ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lDh : zvUs ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsUs : lDh ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lDt : zvUs ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsUs : lDt ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lDg : zvUs ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsUs : lDg ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lDi : zvUs ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsUs : lDi ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lRp : zvUs ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsUs : lRp ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lRn : zvUs ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsUs : lRn ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lFll : zvUs ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsUs : lFll ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lDir : zvUs ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsUs : lDir ≠ zvUs := by decide
@[simp] theorem zv_zsUs_ne_lKb : zvUs ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsUs : lKb ≠ zvUs := by decide
@[simp] theorem zv_zsA_ne_zsU : zvA ≠ zvU := by decide
@[simp] theorem zv_zsA_ne_zsK : zvA ≠ zvK := by decide
@[simp] theorem zv_zsA_ne_zsL : zvA ≠ zvL := by decide
@[simp] theorem zv_zsA_ne_zsUs : zvA ≠ zvUs := by decide
@[simp] theorem zv_zsA_ne_zsB : zvA ≠ zvB := by decide
@[simp] theorem zv_zsA_ne_zsX : zvA ≠ zvX := by decide
@[simp] theorem zv_zsA_ne_zsY : zvA ≠ zvY := by decide
@[simp] theorem zv_zsA_ne_zsN : zvA ≠ zvN := by decide
@[simp] theorem zv_zsA_ne_lFl : zvA ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsA : lFl ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lDh : zvA ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsA : lDh ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lDt : zvA ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsA : lDt ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lDg : zvA ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsA : lDg ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lDi : zvA ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsA : lDi ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lRp : zvA ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsA : lRp ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lRn : zvA ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsA : lRn ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lFll : zvA ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsA : lFll ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lDir : zvA ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsA : lDir ≠ zvA := by decide
@[simp] theorem zv_zsA_ne_lKb : zvA ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsA : lKb ≠ zvA := by decide
@[simp] theorem zv_zsB_ne_zsU : zvB ≠ zvU := by decide
@[simp] theorem zv_zsB_ne_zsK : zvB ≠ zvK := by decide
@[simp] theorem zv_zsB_ne_zsL : zvB ≠ zvL := by decide
@[simp] theorem zv_zsB_ne_zsUs : zvB ≠ zvUs := by decide
@[simp] theorem zv_zsB_ne_zsA : zvB ≠ zvA := by decide
@[simp] theorem zv_zsB_ne_zsX : zvB ≠ zvX := by decide
@[simp] theorem zv_zsB_ne_zsY : zvB ≠ zvY := by decide
@[simp] theorem zv_zsB_ne_zsN : zvB ≠ zvN := by decide
@[simp] theorem zv_zsB_ne_lFl : zvB ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsB : lFl ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lDh : zvB ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsB : lDh ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lDt : zvB ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsB : lDt ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lDg : zvB ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsB : lDg ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lDi : zvB ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsB : lDi ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lRp : zvB ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsB : lRp ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lRn : zvB ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsB : lRn ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lFll : zvB ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsB : lFll ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lDir : zvB ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsB : lDir ≠ zvB := by decide
@[simp] theorem zv_zsB_ne_lKb : zvB ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsB : lKb ≠ zvB := by decide
@[simp] theorem zv_zsX_ne_zsU : zvX ≠ zvU := by decide
@[simp] theorem zv_zsX_ne_zsK : zvX ≠ zvK := by decide
@[simp] theorem zv_zsX_ne_zsL : zvX ≠ zvL := by decide
@[simp] theorem zv_zsX_ne_zsUs : zvX ≠ zvUs := by decide
@[simp] theorem zv_zsX_ne_zsA : zvX ≠ zvA := by decide
@[simp] theorem zv_zsX_ne_zsB : zvX ≠ zvB := by decide
@[simp] theorem zv_zsX_ne_zsY : zvX ≠ zvY := by decide
@[simp] theorem zv_zsX_ne_zsN : zvX ≠ zvN := by decide
@[simp] theorem zv_zsX_ne_lFl : zvX ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsX : lFl ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lDh : zvX ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsX : lDh ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lDt : zvX ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsX : lDt ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lDg : zvX ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsX : lDg ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lDi : zvX ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsX : lDi ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lRp : zvX ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsX : lRp ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lRn : zvX ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsX : lRn ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lFll : zvX ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsX : lFll ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lDir : zvX ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsX : lDir ≠ zvX := by decide
@[simp] theorem zv_zsX_ne_lKb : zvX ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsX : lKb ≠ zvX := by decide
@[simp] theorem zv_zsY_ne_zsU : zvY ≠ zvU := by decide
@[simp] theorem zv_zsY_ne_zsK : zvY ≠ zvK := by decide
@[simp] theorem zv_zsY_ne_zsL : zvY ≠ zvL := by decide
@[simp] theorem zv_zsY_ne_zsUs : zvY ≠ zvUs := by decide
@[simp] theorem zv_zsY_ne_zsA : zvY ≠ zvA := by decide
@[simp] theorem zv_zsY_ne_zsB : zvY ≠ zvB := by decide
@[simp] theorem zv_zsY_ne_zsX : zvY ≠ zvX := by decide
@[simp] theorem zv_zsY_ne_zsN : zvY ≠ zvN := by decide
@[simp] theorem zv_zsY_ne_lFl : zvY ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsY : lFl ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lDh : zvY ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsY : lDh ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lDt : zvY ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsY : lDt ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lDg : zvY ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsY : lDg ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lDi : zvY ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsY : lDi ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lRp : zvY ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsY : lRp ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lRn : zvY ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsY : lRn ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lFll : zvY ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsY : lFll ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lDir : zvY ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsY : lDir ≠ zvY := by decide
@[simp] theorem zv_zsY_ne_lKb : zvY ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsY : lKb ≠ zvY := by decide
@[simp] theorem zv_zsN_ne_zsU : zvN ≠ zvU := by decide
@[simp] theorem zv_zsN_ne_zsK : zvN ≠ zvK := by decide
@[simp] theorem zv_zsN_ne_zsL : zvN ≠ zvL := by decide
@[simp] theorem zv_zsN_ne_zsUs : zvN ≠ zvUs := by decide
@[simp] theorem zv_zsN_ne_zsA : zvN ≠ zvA := by decide
@[simp] theorem zv_zsN_ne_zsB : zvN ≠ zvB := by decide
@[simp] theorem zv_zsN_ne_zsX : zvN ≠ zvX := by decide
@[simp] theorem zv_zsN_ne_zsY : zvN ≠ zvY := by decide
@[simp] theorem zv_zsN_ne_lFl : zvN ≠ lFl := by decide
@[simp] theorem zv_lFl_ne_zsN : lFl ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lDh : zvN ≠ lDh := by decide
@[simp] theorem zv_lDh_ne_zsN : lDh ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lDt : zvN ≠ lDt := by decide
@[simp] theorem zv_lDt_ne_zsN : lDt ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lDg : zvN ≠ lDg := by decide
@[simp] theorem zv_lDg_ne_zsN : lDg ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lDi : zvN ≠ lDi := by decide
@[simp] theorem zv_lDi_ne_zsN : lDi ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lRp : zvN ≠ lRp := by decide
@[simp] theorem zv_lRp_ne_zsN : lRp ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lRn : zvN ≠ lRn := by decide
@[simp] theorem zv_lRn_ne_zsN : lRn ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lFll : zvN ≠ lFll := by decide
@[simp] theorem zv_lFll_ne_zsN : lFll ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lDir : zvN ≠ lDir := by decide
@[simp] theorem zv_lDir_ne_zsN : lDir ≠ zvN := by decide
@[simp] theorem zv_zsN_ne_lKb : zvN ≠ lKb := by decide
@[simp] theorem zv_lKb_ne_zsN : lKb ≠ zvN := by decide

def zvLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zvA, zvB, zvX, zvY, zvN]
def zvParams : List MlS := [zvU, zvK, zvL, zvUs]

def zvBody : ProgHOL 64 := prologue zvLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zvU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local zvN (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, zvX), none)) fZt [vv zvN, vv zvK, vv zvL, vv zvUs, .const 0]) (.return (vv zvX))))
  (.seq (.assign .local zvA (.load .one (vv lRp)))
  (.seq (.assign .local zvB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, zvY), none)) fZv [vv zvB, vv zvK, vv zvL, vv zvUs])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv zvY))
  (.ite (vv zvY) (.seq (.call (some (some (.local, zvX), none)) fZv [vv zvA, vv zvK, vv zvL, vv zvUs]) (.return (vv zvX)))
  (.return (.const 0)))))))))))))


section
variable {σ : Type}

theorem zv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zvLocals → (ctxEnv C ++ zvParams.zip vals).get x = none :=
  Knot.params_none C zvLocals zvParams vals (by decide) (by decide)

theorem zv_spec (C : Ctx) (hcf : C.code.lookup fZv = some (zvParams.map (fun p => (p, ShapeHOL.one)), zvBody, .one))
    (hcp : C.code.lookup fZt = some (ztParams.map (fun p => (p, ShapeHOL.one)), ztBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcz : C.code.lookup fZe0 = some ([(zeU, ShapeHOL.one)], zeBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List ConLeche.Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega))) :
    ∀ (l : ConLeche.Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s (zvParams.zip [Enc.idxW u, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us])) zvBody s
        (pure (zeS ks vs l) : AM Bool) (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (zv_none C _) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zvU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, zvParams, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' zvA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zvB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zvY fZv zvParams [vv zvB, vv zvK, vv zvL, vv zvUs] zvBody
        [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (zeS ks vs _) (by decide) rfl (by decide) hcf
        ⟨by simp, by simp +decide [Env.get, zvParams, ctxEnv], by simp +decide [Env.get, zvParams, ctxEnv],
          by simp +decide [Env.get, zvParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zvParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq : zeS ks vs q
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by simp [zeS, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_callPure zvX fZv zvParams [vv zvA, vv zvK, vv zvL, vv zvUs] zvBody
          [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (zeS ks vs _) (by decide) rfl (by decide) hcf
          ⟨by simp, by simp +decide [Env.get, zvParams, ctxEnv], by simp +decide [Env.get, zvParams, ctxEnv],
            by simp +decide [Env.get, zvParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zvParams _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW (zeS ks vs p)) (by simp)
          (fun t ht => ⟨rfl, by simp [zeS, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' zvA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zvB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zvY fZv zvParams [vv zvB, vv zvK, vv zvL, vv zvUs] zvBody
        [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (zeS ks vs _) (by decide) rfl (by decide) hcf
        ⟨by simp, by simp +decide [Env.get, zvParams, ctxEnv], by simp +decide [Env.get, zvParams, ctxEnv],
          by simp +decide [Env.get, zvParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zvParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW (zeS ks vs q)) (by simp)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' zvN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zvX fZt ztParams [vv zvN, vv zvK, vv zvL, vv zvUs, .const 0] ztBody
        [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 0]
        (ze (ConLeche.Level.subst.go (ks.drop 0) (vs.drop 0) nm)) (by decide) rfl (by decide) hcp
        ⟨by simp, by simp +decide [Env.get, zvParams, ctxEnv], by simp +decide [Env.get, zvParams, ctxEnv],
          by simp +decide [Env.get, zvParams, ctxEnv], rfl, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ztParams _ rfl hlk)
          (zt_spec C hcp hcn hcz s hwf khs ks ok hks hkl hkd hklen us uh vs huv hvl hvd n nm _ hdn _ 0 rfl
            (Nat.zero_le _)))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      exact specR_returnI _ (boolW (ze (ConLeche.Level.subst.go (ks.drop 0) (vs.drop 0) nm))) (by simp)
        (fun t ht => ⟨rfl, by simp [zeS], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
end

end ConPanqueque.T.WC
