import ConPanqueque.T.Core.NzSubst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `zeroWhereZero` over level handles

`zeroWhereZero s u` (is `u` zero wherever `s` is): `s` never zero answers `true`, `u` never zero `false`;
otherwise every parameter of `u`'s zero-ness datum must be one of `s`'s. The datum's parameter list is `zps`
(`zof_eq`); the port walks the level DAG: `zq` (is a name in `zps l`), `za` (all of `zps u` in `zps s`), `zw`.
Read-only.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

/-- The parameters of a level's zero-ness datum (all of them, `never` or not). -/
def zps : Level → List Name
  | .zero => []
  | .succ _ => []
  | .param n => [n]
  | .max a b => zps a ++ zps b
  | .imax _ b => zps b

def zall (s u : Level) : Bool := (zps u).all fun q => (zps s).contains q

theorem zall_max (s a b : Level) : zall s (.max a b) = (zall s a && zall s b) := by
  simp [zall, zps, List.all_append]

theorem zof_eq : ∀ l : Level, nz l = false → ConLeche.Level.zeronessOf l = .ifAllZero (zps l)
  | .zero, _ => rfl
  | .succ _, h => by simp [nz] at h
  | .param _, _ => rfl
  | .max a b, h => by
    simp only [nz, Bool.or_eq_false_iff] at h
    simp [ConLeche.Level.zeronessOf, zof_eq a h.1, zof_eq b h.2, ConLeche.PropWhen.inter, zps]
  | .imax _ b, h => by
    simp only [nz] at h
    simp [ConLeche.Level.zeronessOf, zof_eq b h, zps]

theorem zof_never (l : Level) (h : nz l = true) : ConLeche.Level.zeronessOf l = .never :=
  ConLeche.PropWhen.isNever_iff.mp (by rw [isNever_zeronessOf]; exact h)

theorem zwz_eq (s u : Level) : ConLeche.Level.zeroWhereZero s u = (nz s || (!nz u && zall s u)) := by
  unfold ConLeche.Level.zeroWhereZero
  cases hs : nz s
  · rw [zof_eq s hs]
    cases hu : nz u
    · rw [zof_eq u hu]; simp only [Bool.false_or, Bool.not_false, Bool.true_and, zall]
    · rw [zof_never u hu]; simp
  · rw [zof_never s hs]; simp

def zqQ := ofString "zqn_q"
def zqU := ofString "zqn_u"
def zqN := ofString "zqn_n"
def zqA := ofString "zqn_a"
def zqB := ofString "zqn_b"
def zqX := ofString "zqn_x"
def zqY := ofString "zqn_y"
def zaS := ofString "zan_s"
def zaU := ofString "zan_u"
def zaN := ofString "zan_n"
def zaA := ofString "zan_a"
def zaB := ofString "zan_b"
def zaX := ofString "zan_x"
def zaY := ofString "zan_y"
def zwS := ofString "zwn_s"
def zwU := ofString "zwn_u"
def zwX := ofString "zwn_x"
def zwY := ofString "zwn_y"
def zwZ := ofString "zwn_z"
def fZq := ofString "zeroParamIn"
def fZa := ofString "zeroParamsAll"
def fZw := ofString "zeroWhereZero"

@[simp] theorem lz0_zqQ_ne_zqU : zqQ ≠ zqU := by decide
@[simp] theorem lz0_zqQ_ne_zqN : zqQ ≠ zqN := by decide
@[simp] theorem lz0_zqQ_ne_zqA : zqQ ≠ zqA := by decide
@[simp] theorem lz0_zqQ_ne_zqB : zqQ ≠ zqB := by decide
@[simp] theorem lz0_zqQ_ne_zqX : zqQ ≠ zqX := by decide
@[simp] theorem lz0_zqQ_ne_zqY : zqQ ≠ zqY := by decide
@[simp] theorem lz0_zqQ_ne_lFl : zqQ ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqQ : lFl ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lDh : zqQ ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqQ : lDh ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lDt : zqQ ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqQ : lDt ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lDg : zqQ ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqQ : lDg ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lDi : zqQ ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqQ : lDi ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lRp : zqQ ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqQ : lRp ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lRn : zqQ ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqQ : lRn ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lDir : zqQ ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqQ : lDir ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lFll : zqQ ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqQ : lFll ≠ zqQ := by decide
@[simp] theorem lz0_zqQ_ne_lKb : zqQ ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqQ : lKb ≠ zqQ := by decide
@[simp] theorem lz0_zqU_ne_zqQ : zqU ≠ zqQ := by decide
@[simp] theorem lz0_zqU_ne_zqN : zqU ≠ zqN := by decide
@[simp] theorem lz0_zqU_ne_zqA : zqU ≠ zqA := by decide
@[simp] theorem lz0_zqU_ne_zqB : zqU ≠ zqB := by decide
@[simp] theorem lz0_zqU_ne_zqX : zqU ≠ zqX := by decide
@[simp] theorem lz0_zqU_ne_zqY : zqU ≠ zqY := by decide
@[simp] theorem lz0_zqU_ne_lFl : zqU ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqU : lFl ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lDh : zqU ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqU : lDh ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lDt : zqU ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqU : lDt ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lDg : zqU ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqU : lDg ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lDi : zqU ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqU : lDi ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lRp : zqU ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqU : lRp ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lRn : zqU ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqU : lRn ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lDir : zqU ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqU : lDir ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lFll : zqU ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqU : lFll ≠ zqU := by decide
@[simp] theorem lz0_zqU_ne_lKb : zqU ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqU : lKb ≠ zqU := by decide
@[simp] theorem lz0_zqN_ne_zqQ : zqN ≠ zqQ := by decide
@[simp] theorem lz0_zqN_ne_zqU : zqN ≠ zqU := by decide
@[simp] theorem lz0_zqN_ne_zqA : zqN ≠ zqA := by decide
@[simp] theorem lz0_zqN_ne_zqB : zqN ≠ zqB := by decide
@[simp] theorem lz0_zqN_ne_zqX : zqN ≠ zqX := by decide
@[simp] theorem lz0_zqN_ne_zqY : zqN ≠ zqY := by decide
@[simp] theorem lz0_zqN_ne_lFl : zqN ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqN : lFl ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lDh : zqN ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqN : lDh ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lDt : zqN ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqN : lDt ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lDg : zqN ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqN : lDg ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lDi : zqN ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqN : lDi ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lRp : zqN ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqN : lRp ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lRn : zqN ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqN : lRn ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lDir : zqN ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqN : lDir ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lFll : zqN ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqN : lFll ≠ zqN := by decide
@[simp] theorem lz0_zqN_ne_lKb : zqN ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqN : lKb ≠ zqN := by decide
@[simp] theorem lz0_zqA_ne_zqQ : zqA ≠ zqQ := by decide
@[simp] theorem lz0_zqA_ne_zqU : zqA ≠ zqU := by decide
@[simp] theorem lz0_zqA_ne_zqN : zqA ≠ zqN := by decide
@[simp] theorem lz0_zqA_ne_zqB : zqA ≠ zqB := by decide
@[simp] theorem lz0_zqA_ne_zqX : zqA ≠ zqX := by decide
@[simp] theorem lz0_zqA_ne_zqY : zqA ≠ zqY := by decide
@[simp] theorem lz0_zqA_ne_lFl : zqA ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqA : lFl ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lDh : zqA ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqA : lDh ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lDt : zqA ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqA : lDt ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lDg : zqA ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqA : lDg ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lDi : zqA ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqA : lDi ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lRp : zqA ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqA : lRp ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lRn : zqA ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqA : lRn ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lDir : zqA ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqA : lDir ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lFll : zqA ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqA : lFll ≠ zqA := by decide
@[simp] theorem lz0_zqA_ne_lKb : zqA ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqA : lKb ≠ zqA := by decide
@[simp] theorem lz0_zqB_ne_zqQ : zqB ≠ zqQ := by decide
@[simp] theorem lz0_zqB_ne_zqU : zqB ≠ zqU := by decide
@[simp] theorem lz0_zqB_ne_zqN : zqB ≠ zqN := by decide
@[simp] theorem lz0_zqB_ne_zqA : zqB ≠ zqA := by decide
@[simp] theorem lz0_zqB_ne_zqX : zqB ≠ zqX := by decide
@[simp] theorem lz0_zqB_ne_zqY : zqB ≠ zqY := by decide
@[simp] theorem lz0_zqB_ne_lFl : zqB ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqB : lFl ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lDh : zqB ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqB : lDh ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lDt : zqB ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqB : lDt ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lDg : zqB ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqB : lDg ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lDi : zqB ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqB : lDi ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lRp : zqB ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqB : lRp ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lRn : zqB ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqB : lRn ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lDir : zqB ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqB : lDir ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lFll : zqB ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqB : lFll ≠ zqB := by decide
@[simp] theorem lz0_zqB_ne_lKb : zqB ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqB : lKb ≠ zqB := by decide
@[simp] theorem lz0_zqX_ne_zqQ : zqX ≠ zqQ := by decide
@[simp] theorem lz0_zqX_ne_zqU : zqX ≠ zqU := by decide
@[simp] theorem lz0_zqX_ne_zqN : zqX ≠ zqN := by decide
@[simp] theorem lz0_zqX_ne_zqA : zqX ≠ zqA := by decide
@[simp] theorem lz0_zqX_ne_zqB : zqX ≠ zqB := by decide
@[simp] theorem lz0_zqX_ne_zqY : zqX ≠ zqY := by decide
@[simp] theorem lz0_zqX_ne_lFl : zqX ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqX : lFl ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lDh : zqX ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqX : lDh ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lDt : zqX ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqX : lDt ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lDg : zqX ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqX : lDg ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lDi : zqX ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqX : lDi ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lRp : zqX ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqX : lRp ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lRn : zqX ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqX : lRn ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lDir : zqX ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqX : lDir ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lFll : zqX ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqX : lFll ≠ zqX := by decide
@[simp] theorem lz0_zqX_ne_lKb : zqX ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqX : lKb ≠ zqX := by decide
@[simp] theorem lz0_zqY_ne_zqQ : zqY ≠ zqQ := by decide
@[simp] theorem lz0_zqY_ne_zqU : zqY ≠ zqU := by decide
@[simp] theorem lz0_zqY_ne_zqN : zqY ≠ zqN := by decide
@[simp] theorem lz0_zqY_ne_zqA : zqY ≠ zqA := by decide
@[simp] theorem lz0_zqY_ne_zqB : zqY ≠ zqB := by decide
@[simp] theorem lz0_zqY_ne_zqX : zqY ≠ zqX := by decide
@[simp] theorem lz0_zqY_ne_lFl : zqY ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zqY : lFl ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lDh : zqY ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zqY : lDh ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lDt : zqY ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zqY : lDt ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lDg : zqY ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zqY : lDg ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lDi : zqY ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zqY : lDi ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lRp : zqY ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zqY : lRp ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lRn : zqY ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zqY : lRn ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lDir : zqY ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zqY : lDir ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lFll : zqY ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zqY : lFll ≠ zqY := by decide
@[simp] theorem lz0_zqY_ne_lKb : zqY ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zqY : lKb ≠ zqY := by decide
@[simp] theorem lz0_zaS_ne_zaU : zaS ≠ zaU := by decide
@[simp] theorem lz0_zaS_ne_zaN : zaS ≠ zaN := by decide
@[simp] theorem lz0_zaS_ne_zaA : zaS ≠ zaA := by decide
@[simp] theorem lz0_zaS_ne_zaB : zaS ≠ zaB := by decide
@[simp] theorem lz0_zaS_ne_zaX : zaS ≠ zaX := by decide
@[simp] theorem lz0_zaS_ne_zaY : zaS ≠ zaY := by decide
@[simp] theorem lz0_zaS_ne_lFl : zaS ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaS : lFl ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lDh : zaS ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaS : lDh ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lDt : zaS ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaS : lDt ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lDg : zaS ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaS : lDg ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lDi : zaS ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaS : lDi ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lRp : zaS ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaS : lRp ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lRn : zaS ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaS : lRn ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lDir : zaS ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaS : lDir ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lFll : zaS ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaS : lFll ≠ zaS := by decide
@[simp] theorem lz0_zaS_ne_lKb : zaS ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaS : lKb ≠ zaS := by decide
@[simp] theorem lz0_zaU_ne_zaS : zaU ≠ zaS := by decide
@[simp] theorem lz0_zaU_ne_zaN : zaU ≠ zaN := by decide
@[simp] theorem lz0_zaU_ne_zaA : zaU ≠ zaA := by decide
@[simp] theorem lz0_zaU_ne_zaB : zaU ≠ zaB := by decide
@[simp] theorem lz0_zaU_ne_zaX : zaU ≠ zaX := by decide
@[simp] theorem lz0_zaU_ne_zaY : zaU ≠ zaY := by decide
@[simp] theorem lz0_zaU_ne_lFl : zaU ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaU : lFl ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lDh : zaU ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaU : lDh ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lDt : zaU ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaU : lDt ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lDg : zaU ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaU : lDg ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lDi : zaU ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaU : lDi ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lRp : zaU ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaU : lRp ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lRn : zaU ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaU : lRn ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lDir : zaU ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaU : lDir ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lFll : zaU ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaU : lFll ≠ zaU := by decide
@[simp] theorem lz0_zaU_ne_lKb : zaU ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaU : lKb ≠ zaU := by decide
@[simp] theorem lz0_zaN_ne_zaS : zaN ≠ zaS := by decide
@[simp] theorem lz0_zaN_ne_zaU : zaN ≠ zaU := by decide
@[simp] theorem lz0_zaN_ne_zaA : zaN ≠ zaA := by decide
@[simp] theorem lz0_zaN_ne_zaB : zaN ≠ zaB := by decide
@[simp] theorem lz0_zaN_ne_zaX : zaN ≠ zaX := by decide
@[simp] theorem lz0_zaN_ne_zaY : zaN ≠ zaY := by decide
@[simp] theorem lz0_zaN_ne_lFl : zaN ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaN : lFl ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lDh : zaN ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaN : lDh ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lDt : zaN ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaN : lDt ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lDg : zaN ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaN : lDg ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lDi : zaN ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaN : lDi ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lRp : zaN ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaN : lRp ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lRn : zaN ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaN : lRn ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lDir : zaN ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaN : lDir ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lFll : zaN ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaN : lFll ≠ zaN := by decide
@[simp] theorem lz0_zaN_ne_lKb : zaN ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaN : lKb ≠ zaN := by decide
@[simp] theorem lz0_zaA_ne_zaS : zaA ≠ zaS := by decide
@[simp] theorem lz0_zaA_ne_zaU : zaA ≠ zaU := by decide
@[simp] theorem lz0_zaA_ne_zaN : zaA ≠ zaN := by decide
@[simp] theorem lz0_zaA_ne_zaB : zaA ≠ zaB := by decide
@[simp] theorem lz0_zaA_ne_zaX : zaA ≠ zaX := by decide
@[simp] theorem lz0_zaA_ne_zaY : zaA ≠ zaY := by decide
@[simp] theorem lz0_zaA_ne_lFl : zaA ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaA : lFl ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lDh : zaA ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaA : lDh ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lDt : zaA ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaA : lDt ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lDg : zaA ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaA : lDg ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lDi : zaA ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaA : lDi ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lRp : zaA ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaA : lRp ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lRn : zaA ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaA : lRn ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lDir : zaA ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaA : lDir ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lFll : zaA ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaA : lFll ≠ zaA := by decide
@[simp] theorem lz0_zaA_ne_lKb : zaA ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaA : lKb ≠ zaA := by decide
@[simp] theorem lz0_zaB_ne_zaS : zaB ≠ zaS := by decide
@[simp] theorem lz0_zaB_ne_zaU : zaB ≠ zaU := by decide
@[simp] theorem lz0_zaB_ne_zaN : zaB ≠ zaN := by decide
@[simp] theorem lz0_zaB_ne_zaA : zaB ≠ zaA := by decide
@[simp] theorem lz0_zaB_ne_zaX : zaB ≠ zaX := by decide
@[simp] theorem lz0_zaB_ne_zaY : zaB ≠ zaY := by decide
@[simp] theorem lz0_zaB_ne_lFl : zaB ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaB : lFl ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lDh : zaB ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaB : lDh ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lDt : zaB ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaB : lDt ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lDg : zaB ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaB : lDg ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lDi : zaB ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaB : lDi ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lRp : zaB ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaB : lRp ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lRn : zaB ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaB : lRn ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lDir : zaB ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaB : lDir ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lFll : zaB ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaB : lFll ≠ zaB := by decide
@[simp] theorem lz0_zaB_ne_lKb : zaB ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaB : lKb ≠ zaB := by decide
@[simp] theorem lz0_zaX_ne_zaS : zaX ≠ zaS := by decide
@[simp] theorem lz0_zaX_ne_zaU : zaX ≠ zaU := by decide
@[simp] theorem lz0_zaX_ne_zaN : zaX ≠ zaN := by decide
@[simp] theorem lz0_zaX_ne_zaA : zaX ≠ zaA := by decide
@[simp] theorem lz0_zaX_ne_zaB : zaX ≠ zaB := by decide
@[simp] theorem lz0_zaX_ne_zaY : zaX ≠ zaY := by decide
@[simp] theorem lz0_zaX_ne_lFl : zaX ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaX : lFl ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lDh : zaX ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaX : lDh ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lDt : zaX ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaX : lDt ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lDg : zaX ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaX : lDg ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lDi : zaX ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaX : lDi ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lRp : zaX ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaX : lRp ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lRn : zaX ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaX : lRn ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lDir : zaX ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaX : lDir ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lFll : zaX ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaX : lFll ≠ zaX := by decide
@[simp] theorem lz0_zaX_ne_lKb : zaX ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaX : lKb ≠ zaX := by decide
@[simp] theorem lz0_zaY_ne_zaS : zaY ≠ zaS := by decide
@[simp] theorem lz0_zaY_ne_zaU : zaY ≠ zaU := by decide
@[simp] theorem lz0_zaY_ne_zaN : zaY ≠ zaN := by decide
@[simp] theorem lz0_zaY_ne_zaA : zaY ≠ zaA := by decide
@[simp] theorem lz0_zaY_ne_zaB : zaY ≠ zaB := by decide
@[simp] theorem lz0_zaY_ne_zaX : zaY ≠ zaX := by decide
@[simp] theorem lz0_zaY_ne_lFl : zaY ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zaY : lFl ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lDh : zaY ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zaY : lDh ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lDt : zaY ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zaY : lDt ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lDg : zaY ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zaY : lDg ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lDi : zaY ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zaY : lDi ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lRp : zaY ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zaY : lRp ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lRn : zaY ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zaY : lRn ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lDir : zaY ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zaY : lDir ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lFll : zaY ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zaY : lFll ≠ zaY := by decide
@[simp] theorem lz0_zaY_ne_lKb : zaY ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zaY : lKb ≠ zaY := by decide
@[simp] theorem lz0_zwS_ne_zwU : zwS ≠ zwU := by decide
@[simp] theorem lz0_zwS_ne_zwX : zwS ≠ zwX := by decide
@[simp] theorem lz0_zwS_ne_zwY : zwS ≠ zwY := by decide
@[simp] theorem lz0_zwS_ne_zwZ : zwS ≠ zwZ := by decide
@[simp] theorem lz0_zwS_ne_lFl : zwS ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zwS : lFl ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lDh : zwS ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zwS : lDh ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lDt : zwS ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zwS : lDt ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lDg : zwS ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zwS : lDg ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lDi : zwS ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zwS : lDi ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lRp : zwS ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zwS : lRp ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lRn : zwS ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zwS : lRn ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lDir : zwS ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zwS : lDir ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lFll : zwS ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zwS : lFll ≠ zwS := by decide
@[simp] theorem lz0_zwS_ne_lKb : zwS ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zwS : lKb ≠ zwS := by decide
@[simp] theorem lz0_zwU_ne_zwS : zwU ≠ zwS := by decide
@[simp] theorem lz0_zwU_ne_zwX : zwU ≠ zwX := by decide
@[simp] theorem lz0_zwU_ne_zwY : zwU ≠ zwY := by decide
@[simp] theorem lz0_zwU_ne_zwZ : zwU ≠ zwZ := by decide
@[simp] theorem lz0_zwU_ne_lFl : zwU ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zwU : lFl ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lDh : zwU ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zwU : lDh ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lDt : zwU ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zwU : lDt ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lDg : zwU ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zwU : lDg ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lDi : zwU ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zwU : lDi ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lRp : zwU ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zwU : lRp ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lRn : zwU ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zwU : lRn ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lDir : zwU ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zwU : lDir ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lFll : zwU ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zwU : lFll ≠ zwU := by decide
@[simp] theorem lz0_zwU_ne_lKb : zwU ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zwU : lKb ≠ zwU := by decide
@[simp] theorem lz0_zwX_ne_zwS : zwX ≠ zwS := by decide
@[simp] theorem lz0_zwX_ne_zwU : zwX ≠ zwU := by decide
@[simp] theorem lz0_zwX_ne_zwY : zwX ≠ zwY := by decide
@[simp] theorem lz0_zwX_ne_zwZ : zwX ≠ zwZ := by decide
@[simp] theorem lz0_zwX_ne_lFl : zwX ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zwX : lFl ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lDh : zwX ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zwX : lDh ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lDt : zwX ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zwX : lDt ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lDg : zwX ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zwX : lDg ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lDi : zwX ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zwX : lDi ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lRp : zwX ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zwX : lRp ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lRn : zwX ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zwX : lRn ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lDir : zwX ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zwX : lDir ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lFll : zwX ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zwX : lFll ≠ zwX := by decide
@[simp] theorem lz0_zwX_ne_lKb : zwX ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zwX : lKb ≠ zwX := by decide
@[simp] theorem lz0_zwY_ne_zwS : zwY ≠ zwS := by decide
@[simp] theorem lz0_zwY_ne_zwU : zwY ≠ zwU := by decide
@[simp] theorem lz0_zwY_ne_zwX : zwY ≠ zwX := by decide
@[simp] theorem lz0_zwY_ne_zwZ : zwY ≠ zwZ := by decide
@[simp] theorem lz0_zwY_ne_lFl : zwY ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zwY : lFl ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lDh : zwY ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zwY : lDh ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lDt : zwY ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zwY : lDt ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lDg : zwY ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zwY : lDg ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lDi : zwY ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zwY : lDi ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lRp : zwY ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zwY : lRp ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lRn : zwY ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zwY : lRn ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lDir : zwY ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zwY : lDir ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lFll : zwY ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zwY : lFll ≠ zwY := by decide
@[simp] theorem lz0_zwY_ne_lKb : zwY ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zwY : lKb ≠ zwY := by decide
@[simp] theorem lz0_zwZ_ne_zwS : zwZ ≠ zwS := by decide
@[simp] theorem lz0_zwZ_ne_zwU : zwZ ≠ zwU := by decide
@[simp] theorem lz0_zwZ_ne_zwX : zwZ ≠ zwX := by decide
@[simp] theorem lz0_zwZ_ne_zwY : zwZ ≠ zwY := by decide
@[simp] theorem lz0_zwZ_ne_lFl : zwZ ≠ lFl := by decide
@[simp] theorem lz0_lFl_ne_zwZ : lFl ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lDh : zwZ ≠ lDh := by decide
@[simp] theorem lz0_lDh_ne_zwZ : lDh ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lDt : zwZ ≠ lDt := by decide
@[simp] theorem lz0_lDt_ne_zwZ : lDt ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lDg : zwZ ≠ lDg := by decide
@[simp] theorem lz0_lDg_ne_zwZ : lDg ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lDi : zwZ ≠ lDi := by decide
@[simp] theorem lz0_lDi_ne_zwZ : lDi ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lRp : zwZ ≠ lRp := by decide
@[simp] theorem lz0_lRp_ne_zwZ : lRp ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lRn : zwZ ≠ lRn := by decide
@[simp] theorem lz0_lRn_ne_zwZ : lRn ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lDir : zwZ ≠ lDir := by decide
@[simp] theorem lz0_lDir_ne_zwZ : lDir ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lFll : zwZ ≠ lFll := by decide
@[simp] theorem lz0_lFll_ne_zwZ : lFll ≠ zwZ := by decide
@[simp] theorem lz0_zwZ_ne_lKb : zwZ ≠ lKb := by decide
@[simp] theorem lz0_lKb_ne_zwZ : lKb ≠ zwZ := by decide

def zqParams : List MlS := [zqQ, zqU]
def zqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zqN, zqA, zqB, zqX, zqY]

def zqBody : ProgHOL 64 := prologue zqLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zqU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 0))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 0))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local zqN (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, zqX), none)) NEq.fNeq [vv zqQ, vv zqN]) (.return (vv zqX))))
  (.seq (.assign .local zqA (.load .one (vv lRp)))
  (.seq (.assign .local zqB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, zqY), none)) fZq [vv zqQ, vv zqB])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv zqY))
  (.ite (vv zqY) (.return (.const 1))
  (.seq (.call (some (some (.local, zqX), none)) fZq [vv zqQ, vv zqA]) (.return (vv zqX))))))))))))))

def zaParams : List MlS := [zaS, zaU]
def zaLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zaN, zaA, zaB, zaX, zaY]

def zaBody : ProgHOL 64 := prologue zaLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zaU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local zaN (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, zaX), none)) fZq [vv zaN, vv zaS]) (.return (vv zaX))))
  (.seq (.assign .local zaA (.load .one (vv lRp)))
  (.seq (.assign .local zaB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, zaY), none)) fZa [vv zaS, vv zaB])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv zaY))
  (.ite (vv zaY) (.seq (.call (some (some (.local, zaX), none)) fZa [vv zaS, vv zaA]) (.return (vv zaX)))
    (.return (.const 0)))))))))))))

def zwParams : List MlS := [zwS, zwU]
def zwLocals : List MlS := [zwX, zwY, zwZ]

def zwBody : ProgHOL 64 := prologue zwLocals
  (.seq (.call (some (some (.local, zwX), none)) fNz0 [vv zwS])
  (.ite (vv zwX) (.return (.const 1))
  (.seq (.call (some (some (.local, zwY), none)) fNz0 [vv zwU])
  (.ite (vv zwY) (.return (.const 0))
  (.seq (.call (some (some (.local, zwZ), none)) fZa [vv zwS, vv zwU]) (.return (vv zwZ)))))))

structure ZwCodes (C : Ctx) : Prop where
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  nz0 : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)
  zq : C.code.lookup fZq = some (zqParams.map (fun p => (p, ShapeHOL.one)), zqBody, .one)
  za : C.code.lookup fZa = some (zaParams.map (fun p => (p, ShapeHOL.one)), zaBody, .one)
  zw : C.code.lookup fZw = some (zwParams.map (fun p => (p, ShapeHOL.one)), zwBody, .one)

section
variable {σ : Type}

theorem zq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zqLocals → (ctxEnv C ++ zqParams.zip vals).get x = none :=
  Knot.params_none C zqLocals zqParams vals (by decide) (by decide)
theorem za_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zaLocals → (ctxEnv C ++ zaParams.zip vals).get x = none :=
  Knot.params_none C zaLocals zaParams vals (by decide) (by decide)
theorem zw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zwLocals → (ctxEnv C ++ zwParams.zip vals).get x = none :=
  Knot.params_none C zwLocals zwParams vals (by decide) (by decide)

theorem zq_spec (C : Ctx) (hc : ZwCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (qn : Name) (qh : NIdx)
    (fq : Nat) (hq : denoteNAux s.store.ns fq qh = some qn) :
    ∀ (l : Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s (zqParams.zip [Enc.idxW qh, Enc.idxW u])) zqBody s (pure ((zps l).contains qn) : AM Bool)
        (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (zq_none C _) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zqU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, zqParams, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp [zps, zall], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp [zps, zall], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zqA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zqY fZq zqParams [vv zqQ, vv zqB] zqBody [Enc.idxW qh, Enc.idxW _] ((zps _).contains qn)
        (by decide) rfl (by decide) hc.zq ⟨by simp +decide [Env.get, zqParams, ctxEnv], by simp, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zqParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq2 : (zps q).contains qn
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_callPure zqX fZq zqParams [vv zqQ, vv zqA] zqBody [Enc.idxW qh, Enc.idxW _] ((zps _).contains qn)
          (by decide) rfl (by decide) hc.zq ⟨by simp +decide [Env.get, zqParams, ctxEnv], by simp, trivial⟩
          (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zqParams _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW ((zps p).contains qn)) (by simp)
          (fun t ht => ⟨rfl, by simp [zps] at hq2 ⊢; simp [hq2], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by simp [zps] at hq2 ⊢; simp [hq2], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zqA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zqY fZq zqParams [vv zqQ, vv zqB] zqBody [Enc.idxW qh, Enc.idxW _] ((zps _).contains qn)
        (by decide) rfl (by decide) hc.zq ⟨by simp +decide [Env.get, zqParams, ctxEnv], by simp, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zqParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW ((zps q).contains qn)) (by simp)
        (fun t ht => ⟨rfl, by simp [zps], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zqN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zqX NEq.fNeq [NEq.pNa, NEq.pNb] [vv zqQ, vv zqN] NEq.neqBody [Enc.idxW qh, Enc.idxW n]
        (decide (qn = nm)) (by decide) rfl (by decide) hc.neq ⟨by simp +decide [Env.get, zqParams, ctxEnv], by simp, trivial⟩
        (ExM.PostB C) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [NEq.pNa, NEq.pNb] _ rfl hlk)
          (NEq.neq_spec C hc.neq qn qh n nm fq _ s hq hdn))
        (fun w H1 hp1 ⟨eH1, hw⟩ => ?_)
      subst eH1 hw
      exact specR_returnI _ (boolW (decide (qn = nm))) (by simp)
        (fun t ht => ⟨rfl, by by_cases e : qn = nm <;> simp [zps, e, eq_comm], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)

theorem za_spec (C : Ctx) (hc : ZwCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (ls : Level) (sh : LIdx)
    (hds : denoteL s.store.ls sh = some ls) :
    ∀ (l : Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s (zaParams.zip [Enc.idxW sh, Enc.idxW u])) zaBody s (pure (zall ls l) : AM Bool)
        (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (za_none C _) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zaU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, zaParams, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp [zps, zall], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp [zps, zall], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zaA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zaB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zaY fZa zaParams [vv zaS, vv zaB] zaBody [Enc.idxW sh, Enc.idxW _] (zall ls _)
        (by decide) rfl (by decide) hc.za ⟨by simp +decide [Env.get, zaParams, ctxEnv], by simp, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zaParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq2 : zall ls q
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by rw [zall_max, hq2]; simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_callPure zaX fZa zaParams [vv zaS, vv zaA] zaBody [Enc.idxW sh, Enc.idxW _] (zall ls _)
          (by decide) rfl (by decide) hc.za ⟨by simp +decide [Env.get, zaParams, ctxEnv], by simp, trivial⟩
          (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zaParams _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW (zall ls p)) (by simp)
          (fun t ht => ⟨rfl, by rw [zall_max, hq2]; simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zaA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zaB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zaY fZa zaParams [vv zaS, vv zaB] zaBody [Enc.idxW sh, Enc.idxW _] (zall ls _)
        (by decide) rfl (by decide) hc.za ⟨by simp +decide [Env.get, zaParams, ctxEnv], by simp, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zaParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW (zall ls q)) (by simp)
        (fun t ht => ⟨rfl, by simp [zall, zps], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
      refine specR_loadI' zaN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zaX fZq zqParams [vv zaN, vv zaS] zqBody [Enc.idxW n, Enc.idxW sh] ((zps ls).contains nm)
        (by decide) rfl (by decide) hc.zq ⟨by simp, by simp +decide [Env.get, zaParams, ctxEnv], trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zqParams _ rfl hlk)
          (zq_spec C hc s hwf nm n _ hdn ls sh hds))
        (fun w H1 hp1 ⟨eH1, hw⟩ => ?_)
      subst eH1 hw
      exact specR_returnI _ (boolW ((zps ls).contains nm)) (by simp)
        (fun t ht => ⟨rfl, by simp [zall, zps], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)

theorem zw_spec (C : Ctx) (hc : ZwCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (ls lu : Level) (sh uh : LIdx)
    (hds : denoteL s.store.ls sh = some ls) (hdu : denoteL s.store.ls uh = some lu) :
    SpecR (σ := σ) (Pre C s (zwParams.zip [Enc.idxW sh, Enc.idxW uh])) zwBody s
      (pure (ConLeche.Level.zeroWhereZero ls lu) : AM Bool) (PostBS C s) := by
  refine specR_prologue (postBS_locals C s) (zw_none C _) ?_
  rw [zwz_eq]
  refine specR_callPure zwX fNz0 [nzU] [vv zwS] nzBody [Enc.idxW sh] (nz ls) (by decide) rfl (by decide) hc.nz0
    ⟨by simp +decide [Env.get, zwParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
    (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk) (nz0_spec C hc.nz0 s hwf ls sh hds))
    (fun w H1 hp1 ⟨eH1, hw⟩ => ?_)
  subst eH1 hw
  cases hs : nz ls
  · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure zwY fNz0 [nzU] [vv zwU] nzBody [Enc.idxW uh] (nz lu) (by decide) rfl (by decide) hc.nz0
      ⟨by simp +decide [Env.get, zwParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
      (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk) (nz0_spec C hc.nz0 s hwf lu uh hdu))
      (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
    subst eH2 hw
    cases hu : nz lu
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_callPure zwZ fZa zaParams [vv zwS, vv zwU] zaBody [Enc.idxW sh, Enc.idxW uh] (zall ls lu)
        (by decide) rfl (by decide) hc.za
        ⟨by simp +decide [Env.get, zwParams, ctxEnv], by simp +decide [Env.get, zwParams, ctxEnv], trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zaParams _ rfl hlk) (za_spec C hc s hwf ls sh hds lu uh hdu))
        (fun w H3 hp3 ⟨eH3, hw⟩ => ?_)
      subst eH3 hw
      exact specR_returnI _ (boolW (zall ls lu)) (by simp) (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW true) (by simp [boolW]; rfl) (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
