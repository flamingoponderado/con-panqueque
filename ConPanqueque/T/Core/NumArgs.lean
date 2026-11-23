import ConPanqueque.T.Core.QuickDefEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `numArgs`

The length of an application spine, by fuel: an `app` handle counts one more than its function.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def naF := ofString "nan_f"
def naH := ofString "nan_h"
def naX := ofString "nan_x"
def naN := ofString "nan_n"
def fNa := ofString "numArgs"

@[simp] theorem na_naF_ne_naH : naF ≠ naH := by decide
@[simp] theorem na_naF_ne_naX : naF ≠ naX := by decide
@[simp] theorem na_naF_ne_naN : naF ≠ naN := by decide
@[simp] theorem na_naF_ne_lFl : naF ≠ lFl := by decide
@[simp] theorem na_lFl_ne_naF : lFl ≠ naF := by decide
@[simp] theorem na_naF_ne_lDh : naF ≠ lDh := by decide
@[simp] theorem na_lDh_ne_naF : lDh ≠ naF := by decide
@[simp] theorem na_naF_ne_lDt : naF ≠ lDt := by decide
@[simp] theorem na_lDt_ne_naF : lDt ≠ naF := by decide
@[simp] theorem na_naF_ne_lDg : naF ≠ lDg := by decide
@[simp] theorem na_lDg_ne_naF : lDg ≠ naF := by decide
@[simp] theorem na_naF_ne_lDi : naF ≠ lDi := by decide
@[simp] theorem na_lDi_ne_naF : lDi ≠ naF := by decide
@[simp] theorem na_naF_ne_lRp : naF ≠ lRp := by decide
@[simp] theorem na_lRp_ne_naF : lRp ≠ naF := by decide
@[simp] theorem na_naF_ne_lRn : naF ≠ lRn := by decide
@[simp] theorem na_lRn_ne_naF : lRn ≠ naF := by decide
@[simp] theorem na_naF_ne_lDir : naF ≠ lDir := by decide
@[simp] theorem na_lDir_ne_naF : lDir ≠ naF := by decide
@[simp] theorem na_naF_ne_lFle : naF ≠ lFle := by decide
@[simp] theorem na_lFle_ne_naF : lFle ≠ naF := by decide
@[simp] theorem na_naF_ne_lKb : naF ≠ lKb := by decide
@[simp] theorem na_lKb_ne_naF : lKb ≠ naF := by decide
@[simp] theorem na_naH_ne_naF : naH ≠ naF := by decide
@[simp] theorem na_naH_ne_naX : naH ≠ naX := by decide
@[simp] theorem na_naH_ne_naN : naH ≠ naN := by decide
@[simp] theorem na_naH_ne_lFl : naH ≠ lFl := by decide
@[simp] theorem na_lFl_ne_naH : lFl ≠ naH := by decide
@[simp] theorem na_naH_ne_lDh : naH ≠ lDh := by decide
@[simp] theorem na_lDh_ne_naH : lDh ≠ naH := by decide
@[simp] theorem na_naH_ne_lDt : naH ≠ lDt := by decide
@[simp] theorem na_lDt_ne_naH : lDt ≠ naH := by decide
@[simp] theorem na_naH_ne_lDg : naH ≠ lDg := by decide
@[simp] theorem na_lDg_ne_naH : lDg ≠ naH := by decide
@[simp] theorem na_naH_ne_lDi : naH ≠ lDi := by decide
@[simp] theorem na_lDi_ne_naH : lDi ≠ naH := by decide
@[simp] theorem na_naH_ne_lRp : naH ≠ lRp := by decide
@[simp] theorem na_lRp_ne_naH : lRp ≠ naH := by decide
@[simp] theorem na_naH_ne_lRn : naH ≠ lRn := by decide
@[simp] theorem na_lRn_ne_naH : lRn ≠ naH := by decide
@[simp] theorem na_naH_ne_lDir : naH ≠ lDir := by decide
@[simp] theorem na_lDir_ne_naH : lDir ≠ naH := by decide
@[simp] theorem na_naH_ne_lFle : naH ≠ lFle := by decide
@[simp] theorem na_lFle_ne_naH : lFle ≠ naH := by decide
@[simp] theorem na_naH_ne_lKb : naH ≠ lKb := by decide
@[simp] theorem na_lKb_ne_naH : lKb ≠ naH := by decide
@[simp] theorem na_naX_ne_naF : naX ≠ naF := by decide
@[simp] theorem na_naX_ne_naH : naX ≠ naH := by decide
@[simp] theorem na_naX_ne_naN : naX ≠ naN := by decide
@[simp] theorem na_naX_ne_lFl : naX ≠ lFl := by decide
@[simp] theorem na_lFl_ne_naX : lFl ≠ naX := by decide
@[simp] theorem na_naX_ne_lDh : naX ≠ lDh := by decide
@[simp] theorem na_lDh_ne_naX : lDh ≠ naX := by decide
@[simp] theorem na_naX_ne_lDt : naX ≠ lDt := by decide
@[simp] theorem na_lDt_ne_naX : lDt ≠ naX := by decide
@[simp] theorem na_naX_ne_lDg : naX ≠ lDg := by decide
@[simp] theorem na_lDg_ne_naX : lDg ≠ naX := by decide
@[simp] theorem na_naX_ne_lDi : naX ≠ lDi := by decide
@[simp] theorem na_lDi_ne_naX : lDi ≠ naX := by decide
@[simp] theorem na_naX_ne_lRp : naX ≠ lRp := by decide
@[simp] theorem na_lRp_ne_naX : lRp ≠ naX := by decide
@[simp] theorem na_naX_ne_lRn : naX ≠ lRn := by decide
@[simp] theorem na_lRn_ne_naX : lRn ≠ naX := by decide
@[simp] theorem na_naX_ne_lDir : naX ≠ lDir := by decide
@[simp] theorem na_lDir_ne_naX : lDir ≠ naX := by decide
@[simp] theorem na_naX_ne_lFle : naX ≠ lFle := by decide
@[simp] theorem na_lFle_ne_naX : lFle ≠ naX := by decide
@[simp] theorem na_naX_ne_lKb : naX ≠ lKb := by decide
@[simp] theorem na_lKb_ne_naX : lKb ≠ naX := by decide
@[simp] theorem na_naN_ne_naF : naN ≠ naF := by decide
@[simp] theorem na_naN_ne_naH : naN ≠ naH := by decide
@[simp] theorem na_naN_ne_naX : naN ≠ naX := by decide
@[simp] theorem na_naN_ne_lFl : naN ≠ lFl := by decide
@[simp] theorem na_lFl_ne_naN : lFl ≠ naN := by decide
@[simp] theorem na_naN_ne_lDh : naN ≠ lDh := by decide
@[simp] theorem na_lDh_ne_naN : lDh ≠ naN := by decide
@[simp] theorem na_naN_ne_lDt : naN ≠ lDt := by decide
@[simp] theorem na_lDt_ne_naN : lDt ≠ naN := by decide
@[simp] theorem na_naN_ne_lDg : naN ≠ lDg := by decide
@[simp] theorem na_lDg_ne_naN : lDg ≠ naN := by decide
@[simp] theorem na_naN_ne_lDi : naN ≠ lDi := by decide
@[simp] theorem na_lDi_ne_naN : lDi ≠ naN := by decide
@[simp] theorem na_naN_ne_lRp : naN ≠ lRp := by decide
@[simp] theorem na_lRp_ne_naN : lRp ≠ naN := by decide
@[simp] theorem na_naN_ne_lRn : naN ≠ lRn := by decide
@[simp] theorem na_lRn_ne_naN : lRn ≠ naN := by decide
@[simp] theorem na_naN_ne_lDir : naN ≠ lDir := by decide
@[simp] theorem na_lDir_ne_naN : lDir ≠ naN := by decide
@[simp] theorem na_naN_ne_lFle : naN ≠ lFle := by decide
@[simp] theorem na_lFle_ne_naN : lFle ≠ naN := by decide
@[simp] theorem na_naN_ne_lKb : naN ≠ lKb := by decide
@[simp] theorem na_lKb_ne_naN : lKb ≠ naN := by decide

def naParams : List MlS := [naF, naH]
def naLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, naX, naN]
def naBody : ProgHOL 64 := prologue naLocals (.ite (.cmp .equal (vv naF) (.const 0)) hang (.ite (tagIs4E naH) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv naH)) (.seq eViewP (.seq (.assign .local naX (.load .one (vv lRp))) (.seq (.call (some (some (.local, naN), none)) fNa [(.op .sub [(vv naF), (.const 1)]), (vv naX)]) (.return (.op .add [(vv naN), (.const 1)]))))))) (.return (.const 0))))

section
variable {σ : Type}

/-- A natural number answer below the fuel, the state unchanged. -/
def PostNa (C : Ctx) (s : AState) (fuel : Nat) (a : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ a ≤ fuel ∧ w = BitVec.ofNat 64 a ∧ SR C s st

theorem postNa_locals (C : Ctx) (s : AState) (fuel : Nat) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostNa C s fuel a w s' st → PostNa C s fuel a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem na_spec (C : Ctx) (hcf : C.code.lookup fNa = some (naParams.map (fun p => (p, ShapeHOL.one)), naBody, .one)) :
    ∀ fuel (h : EIdx) (s : AState), fuel < 2 ^ 63 →
      SpecR (σ := σ) (Pre C s (naParams.zip [BitVec.ofNat 64 fuel, Enc.idxW h])) naBody s (numArgs fuel h)
        (PostNa C s fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h s _
    refine specR_prologue (postNa_locals C s 0) (Knot.params_none C naLocals naParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, naParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ k ih =>
    intro h s hk
    refine specR_prologue (postNa_locals C s (k + 1)) (Knot.params_none C naLocals naParams _ (by decide) (by decide)) ?_
    rw [numArgs]
    have hne := ofNat_succ_ne k (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, naParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_tag4IteE naH h (by simp +decide [Env.get, naParams, ctxEnv]) (fun ht4 => ?_) (fun ht4 => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.app) = true by simpa [ETag.app] using ht4)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by omega, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.app) = true by simp [ht4, ETag.app])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv naH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, naParams, ctxEnv]) ?_
    refine specR_viewAppI h ht4 (by simp) (by simp +decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun f a P => ?_)
    dsimp only
    refine specR_loadI' naX _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
    refine specR_dropM ?_
    refine specR_callNIH (C := C) naN fNa naParams [.op .sub [vv naF, .const 1], vv naX] naBody
      [BitVec.ofNat 64 k, Enc.idxW f] (by decide) rfl (by decide) hcf
      ⟨by simp +decide [sev, Env.get, naParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
      (PostNa C s k) (fun a w s' H' => s' = s ∧ a ≤ k ∧ w = BitVec.ofNat 64 a ∧ H' = C.H)
      (fun a w s' st ⟨h1, h2, h3, h4⟩ => ⟨C.H, List.prefix_refl _, ⟨h1, h2, h3, rfl⟩, by subst h1; exact h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu naParams _ rfl hlk) (ih f s (by omega)))
      (fun m w s1 H1 _ ⟨hs1, hm, hw, eH⟩ => ?_)
    subst hs1 hw
    exact specR_returnI _ (BitVec.ofNat 64 (m + 1)) (by simp [sev]; exact word_add1_eq m)
      (fun t ht => ⟨rfl, by omega, rfl, by subst eH; exact sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
