import ConPanqueque.T.Core.InferApp
import ConPanqueque.T.Big.NatBin
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The literal arm: `inferLit`

A `Nat` numeral (row word `0`) under the `natLit` flag, not above the run's maximum `Nat` size, has type the
constant `Nat`; a string literal (row word `1`) under the `strLit` flag has type `String`. The twin's failures
(a flag off, a refused numeral) are halts.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ilW := ofString "iln_w"
def ilL := ofString "iln_l"
def ilN := ofString "iln_n"
def ilM := ofString "iln_m"
def ilS := ofString "iln_s"
def ilT := ofString "iln_t"
def ilR := ofString "iln_r"

@[simp] theorem il_ilW_ne_ilL : ilW ≠ ilL := by decide
@[simp] theorem il_ilW_ne_ilN : ilW ≠ ilN := by decide
@[simp] theorem il_ilW_ne_ilM : ilW ≠ ilM := by decide
@[simp] theorem il_ilW_ne_ilS : ilW ≠ ilS := by decide
@[simp] theorem il_ilW_ne_ilT : ilW ≠ ilT := by decide
@[simp] theorem il_ilW_ne_ilR : ilW ≠ ilR := by decide
@[simp] theorem il_ilW_ne_ibE : ilW ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilW : ibE ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lFl : ilW ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilW : lFl ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lDh : ilW ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilW : lDh ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lDt : ilW ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilW : lDt ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lDg : ilW ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilW : lDg ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lDi : ilW ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilW : lDi ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lRp : ilW ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilW : lRp ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lRn : ilW ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilW : lRn ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lDir : ilW ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilW : lDir ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lFle : ilW ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilW : lFle ≠ ilW := by decide
@[simp] theorem il_ilW_ne_lKb : ilW ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilW : lKb ≠ ilW := by decide
@[simp] theorem il_ilL_ne_ilW : ilL ≠ ilW := by decide
@[simp] theorem il_ilL_ne_ilN : ilL ≠ ilN := by decide
@[simp] theorem il_ilL_ne_ilM : ilL ≠ ilM := by decide
@[simp] theorem il_ilL_ne_ilS : ilL ≠ ilS := by decide
@[simp] theorem il_ilL_ne_ilT : ilL ≠ ilT := by decide
@[simp] theorem il_ilL_ne_ilR : ilL ≠ ilR := by decide
@[simp] theorem il_ilL_ne_ibE : ilL ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilL : ibE ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lFl : ilL ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilL : lFl ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lDh : ilL ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilL : lDh ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lDt : ilL ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilL : lDt ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lDg : ilL ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilL : lDg ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lDi : ilL ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilL : lDi ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lRp : ilL ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilL : lRp ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lRn : ilL ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilL : lRn ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lDir : ilL ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilL : lDir ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lFle : ilL ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilL : lFle ≠ ilL := by decide
@[simp] theorem il_ilL_ne_lKb : ilL ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilL : lKb ≠ ilL := by decide
@[simp] theorem il_ilN_ne_ilW : ilN ≠ ilW := by decide
@[simp] theorem il_ilN_ne_ilL : ilN ≠ ilL := by decide
@[simp] theorem il_ilN_ne_ilM : ilN ≠ ilM := by decide
@[simp] theorem il_ilN_ne_ilS : ilN ≠ ilS := by decide
@[simp] theorem il_ilN_ne_ilT : ilN ≠ ilT := by decide
@[simp] theorem il_ilN_ne_ilR : ilN ≠ ilR := by decide
@[simp] theorem il_ilN_ne_ibE : ilN ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilN : ibE ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lFl : ilN ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilN : lFl ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lDh : ilN ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilN : lDh ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lDt : ilN ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilN : lDt ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lDg : ilN ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilN : lDg ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lDi : ilN ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilN : lDi ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lRp : ilN ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilN : lRp ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lRn : ilN ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilN : lRn ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lDir : ilN ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilN : lDir ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lFle : ilN ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilN : lFle ≠ ilN := by decide
@[simp] theorem il_ilN_ne_lKb : ilN ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilN : lKb ≠ ilN := by decide
@[simp] theorem il_ilM_ne_ilW : ilM ≠ ilW := by decide
@[simp] theorem il_ilM_ne_ilL : ilM ≠ ilL := by decide
@[simp] theorem il_ilM_ne_ilN : ilM ≠ ilN := by decide
@[simp] theorem il_ilM_ne_ilS : ilM ≠ ilS := by decide
@[simp] theorem il_ilM_ne_ilT : ilM ≠ ilT := by decide
@[simp] theorem il_ilM_ne_ilR : ilM ≠ ilR := by decide
@[simp] theorem il_ilM_ne_ibE : ilM ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilM : ibE ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lFl : ilM ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilM : lFl ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lDh : ilM ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilM : lDh ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lDt : ilM ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilM : lDt ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lDg : ilM ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilM : lDg ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lDi : ilM ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilM : lDi ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lRp : ilM ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilM : lRp ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lRn : ilM ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilM : lRn ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lDir : ilM ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilM : lDir ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lFle : ilM ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilM : lFle ≠ ilM := by decide
@[simp] theorem il_ilM_ne_lKb : ilM ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilM : lKb ≠ ilM := by decide
@[simp] theorem il_ilS_ne_ilW : ilS ≠ ilW := by decide
@[simp] theorem il_ilS_ne_ilL : ilS ≠ ilL := by decide
@[simp] theorem il_ilS_ne_ilN : ilS ≠ ilN := by decide
@[simp] theorem il_ilS_ne_ilM : ilS ≠ ilM := by decide
@[simp] theorem il_ilS_ne_ilT : ilS ≠ ilT := by decide
@[simp] theorem il_ilS_ne_ilR : ilS ≠ ilR := by decide
@[simp] theorem il_ilS_ne_ibE : ilS ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilS : ibE ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lFl : ilS ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilS : lFl ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lDh : ilS ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilS : lDh ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lDt : ilS ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilS : lDt ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lDg : ilS ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilS : lDg ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lDi : ilS ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilS : lDi ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lRp : ilS ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilS : lRp ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lRn : ilS ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilS : lRn ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lDir : ilS ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilS : lDir ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lFle : ilS ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilS : lFle ≠ ilS := by decide
@[simp] theorem il_ilS_ne_lKb : ilS ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilS : lKb ≠ ilS := by decide
@[simp] theorem il_ilT_ne_ilW : ilT ≠ ilW := by decide
@[simp] theorem il_ilT_ne_ilL : ilT ≠ ilL := by decide
@[simp] theorem il_ilT_ne_ilN : ilT ≠ ilN := by decide
@[simp] theorem il_ilT_ne_ilM : ilT ≠ ilM := by decide
@[simp] theorem il_ilT_ne_ilS : ilT ≠ ilS := by decide
@[simp] theorem il_ilT_ne_ilR : ilT ≠ ilR := by decide
@[simp] theorem il_ilT_ne_ibE : ilT ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilT : ibE ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lFl : ilT ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilT : lFl ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lDh : ilT ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilT : lDh ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lDt : ilT ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilT : lDt ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lDg : ilT ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilT : lDg ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lDi : ilT ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilT : lDi ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lRp : ilT ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilT : lRp ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lRn : ilT ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilT : lRn ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lDir : ilT ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilT : lDir ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lFle : ilT ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilT : lFle ≠ ilT := by decide
@[simp] theorem il_ilT_ne_lKb : ilT ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilT : lKb ≠ ilT := by decide
@[simp] theorem il_ilR_ne_ilW : ilR ≠ ilW := by decide
@[simp] theorem il_ilR_ne_ilL : ilR ≠ ilL := by decide
@[simp] theorem il_ilR_ne_ilN : ilR ≠ ilN := by decide
@[simp] theorem il_ilR_ne_ilM : ilR ≠ ilM := by decide
@[simp] theorem il_ilR_ne_ilS : ilR ≠ ilS := by decide
@[simp] theorem il_ilR_ne_ilT : ilR ≠ ilT := by decide
@[simp] theorem il_ilR_ne_ibE : ilR ≠ ibE := by decide
@[simp] theorem il_ibE_ne_ilR : ibE ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lFl : ilR ≠ lFl := by decide
@[simp] theorem il_lFl_ne_ilR : lFl ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lDh : ilR ≠ lDh := by decide
@[simp] theorem il_lDh_ne_ilR : lDh ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lDt : ilR ≠ lDt := by decide
@[simp] theorem il_lDt_ne_ilR : lDt ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lDg : ilR ≠ lDg := by decide
@[simp] theorem il_lDg_ne_ilR : lDg ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lDi : ilR ≠ lDi := by decide
@[simp] theorem il_lDi_ne_ilR : lDi ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lRp : ilR ≠ lRp := by decide
@[simp] theorem il_lRp_ne_ilR : lRp ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lRn : ilR ≠ lRn := by decide
@[simp] theorem il_lRn_ne_ilR : lRn ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lDir : ilR ≠ lDir := by decide
@[simp] theorem il_lDir_ne_ilR : lDir ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lFle : ilR ≠ lFle := by decide
@[simp] theorem il_lFle_ne_ilR : lFle ≠ ilR := by decide
@[simp] theorem il_ilR_ne_lKb : ilR ≠ lKb := by decide
@[simp] theorem il_lKb_ne_ilR : lKb ≠ ilR := by decide

def ilLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ilW, ilL, ilN, ilM, ilS, ilT, ilR]

def ilSizeE : ExpHOL 64 :=
  .panop .mul [.op .add [vv ilN, .cmp .equal (vv ilN) (.const 0)], .const 8]

def ilConst (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local ilT (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
  (.seq (.call (some (some (.local, ilR), none)) fInternConst [vv ilS, vv ilT]) (.return (vv ilR)))

def ilCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ibE)) (.seq eViewP
  (.seq (.assign .local ilW (.load .one (vv lRp)))
  (.seq (.assign .local ilL (.var .global gLit))
  (.ite (.cmp .equal (vv ilW) (.const 0))
    (.ite (.op .and [vv ilL, .const 1])
      (.seq (.assign .local ilN (.op .sub [vv lRn, .const 1]))
      (.seq (.assign .local ilM (.load .one (.const (ecell C (C.PO + pinCount + 3)))))
      (.ite (.cmp .lower (vv ilM) ilSizeE) hang
        (.seq (.assign .local ilS (.load .one (.const (ecell C (C.PO + PIN_NAT))))) (ilConst C)))))
      hang)
    (.ite (.op .and [vv ilL, .const 2])
      (.seq (.assign .local ilS (.load .one (.const (ecell C (C.PO + PIN_STRING))))) (ilConst C))
      hang))))))

def ilBody (C : Ctx) : ProgHOL 64 := prologue ilLocals (ilCore C)

section
variable {σ : Type}

theorem il_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ilLocals → (ctxEnv C ++ iblParams.zip vals).get x = none :=
  Knot.params_none C ilLocals iblParams vals (by decide) (by decide)

theorem sev_ilSize (Γ : Env) (len : Nat) (hl : len < 2 ^ 61) (h : Γ.get ilN = some (BitVec.ofNat 64 len)) :
    sev Γ ilSizeE = some (BitVec.ofNat 64 (8 * max len 1)) := by
  simp only [ilSizeE, sev, vv, h]
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  apply BitVec.eq_of_toNat_eq
  by_cases h0 : len = 0
  · subst h0; simp
  · have : BitVec.ofNat 64 len ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp [this, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.max_eq_left (by omega)]; omega

theorem il_const (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    {s : AState} {Γ : Env} {D : List MlS} (n : NIdx) (hS : Γ.get ilS = some (Enc.idxW n)) (hD : ilT ∈ D ∧ ilR ∈ D) :
    SpecR (σ := σ) (Inv C s Γ [] D) (ilConst C) s (constE n) (PostK C) := by
  refine specR_congr (m' := emptyLevels >>= fun us => internConstE n us >>= fun x => pure x)
    (by simp only [constE, bind_pure]; rfl) ?_
  refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
    (pin_emptyLevels_cell hok) ilT hD.1 ?_
  refine ILP.callE_spec ilR fInternConst [lEn, lEus] [vv ilS, vv ilT] constBody
    [Enc.idxW n, Enc.idxW C.pins.emptyLevels] (by decide) rfl hD.2 hcic
    ⟨by simp [hS], by simp, trivial⟩ (const_body_spec ra C hok s n C.pins.emptyLevels) (fun h s' => ?_)
  exact specR_returnI _ (Enc.idxW h) (by simp) (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_ilSizeIte {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (len maxN : Nat) (hl : len < 2 ^ 61)
    (hm : maxN < 2 ^ 64) (h1 : Γ.get ilM = some (BitVec.ofNat 64 maxN)) (h2 : Γ.get ilN = some (BitVec.ofNat 64 len))
    (hk : 8 * max len 1 ≤ maxN → SpecR (Inv C s Γ M D) c s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .lower (vv ilM) ilSizeE) hang c) s m R := by
  have hsz := sev_ilSize Γ len hl h2
  have hlt := word_lt_iff maxN (8 * max len 1) (by unfold B; omega) (by unfold B; omega)
  by_cases hc : maxN < 8 * max len 1
  · exact specR_ifI _ 1 (by simp [sev, sev_vv, hsz, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hc])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  · exact specR_ifI _ 0 (by simp [sev, sev_vv, hsz, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlt).mpr hc]) (fun h => absurd rfl h) (fun _ => hk (by omega))

theorem il_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (s : AState) (e : EIdx) (l : ConLeche.Literal) (hvl : s.store.view e = some (.lit l)) :
    SpecR (σ := σ) (Pre C s (iblParams.zip [Enc.idxW e])) (ilBody C) s (ibLitT C.fe l) (PostK C) := by
  refine specR_prologue (postK_locals C) (il_none C _) ?_
  unfold ilCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv ibE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, iblParams, ctxEnv]) ?_
  refine specR_congr (m' := ConRon.Arena.view e >>= fun _ => ibLitT C.fe l) (view_bind_eq e (.lit l) (fun _ => ibLitT C.fe l) s hvl).symm ?_
  refine ILP.specR_viewIv e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv _ hlen => ?_)
  rw [hvl] at hv
  cases hv
  cases l with
  | natVal m =>
    refine specR_loadI' ilW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
    refine specR_dropM ?_
    refine specR_gLitI ilL (by decide) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold ibLitT
    dsimp only
    by_cases hnl : C.fe.natLit = true
    swap
    · have hf : C.fe.natLit = false := by simpa using hnl
      refine specR_ifI _ 0 (by simp [sev, litW_and1, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI
    refine specR_ifI _ 1 (by simp [sev, litW_and1, hnl, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [ite_eq_left hnl]
    have hlen' : (limbs m).length + 1 < 2 ^ 61 := by simpa [encEView, Enc.encLit] using hlen
    refine specR_assignI ilN _ (BitVec.ofNat 64 (limbs m).length) (by decide)
      (by simp [sev, encEView, Enc.encLit]; exact Ex.ofNat_succ_sub_one _) ?_
    have hpm := hok.pinsRel.2.2.2.2.2.1
    refine specR_envLoadI ilM _ (C.PO + pinCount + 3) _ (by decide) rfl hpm.1 ?_
    refine specR_ilSizeIte (limbs m).length C.pins.maxNatSize (by omega) (by have := hpm.2; omega) ?_ ?_
      (fun hle => ?_)
    · simp
    · simp
    refine specR_atEntry fun t ht => ?_
    have hp : s.pins = C.pins := ht.sr.pins
    refine specR_runBind (natSizeRefused_run m s) ?_
    have e : decide (natSizeBytes m > s.pins.maxNatSize) = false := by
      rw [hp, natSizeBytes_limbs]; simp; omega
    simp only [e, Bool.false_eq_true, ↓reduceIte]
    unfold pinNat
    refine specR_pinAtI hok PIN_NAT (by decide) ilS (by decide) ?_
    exact il_const ra hok hcic _ (by simp) ⟨by decide, by decide⟩
  | strVal str =>
    refine specR_loadI' ilW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
    refine specR_dropM ?_
    refine specR_gLitI ilL (by decide) ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    unfold ibLitT
    dsimp only
    by_cases hsl : C.fe.strLit = true
    · refine specR_ifI _ 2 (by simp [sev, litW_and2, hsl, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [ite_eq_left hsl]
      unfold pinString
      refine specR_pinAtI hok PIN_STRING (by decide) ilS (by decide) ?_
      exact il_const ra hok hcic _ (by simp) ⟨by decide, by decide⟩
    · have hf : C.fe.strLit = false := by simpa using hsl
      refine specR_ifI _ 0 (by simp [sev, litW_and2, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI

end

end ConPanqueque.T.WC
