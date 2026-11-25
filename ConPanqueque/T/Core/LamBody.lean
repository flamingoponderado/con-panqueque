import ConPanqueque.T.Core.IotaBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `lamBody`: the body under `k` leading λs

A recursive function over `k`: a `lam` handle recurses on its body; anything else (or `k = 0`) is returned.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def lbK := ofString "lbk"
def lbH := ofString "lbh"
def lbB := ofString "lbb"
def lbR := ofString "lbr"
def fLb := ofString "lamBody"

@[simp] theorem lb_lbK_ne_lbH : lbK ≠ lbH := by decide
@[simp] theorem lb_lbK_ne_lbB : lbK ≠ lbB := by decide
@[simp] theorem lb_lbK_ne_lbR : lbK ≠ lbR := by decide
@[simp] theorem lb_lbK_ne_lFl : lbK ≠ lFl := by decide
@[simp] theorem lb_lFl_ne_lbK : lFl ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lDh : lbK ≠ lDh := by decide
@[simp] theorem lb_lDh_ne_lbK : lDh ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lDt : lbK ≠ lDt := by decide
@[simp] theorem lb_lDt_ne_lbK : lDt ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lDg : lbK ≠ lDg := by decide
@[simp] theorem lb_lDg_ne_lbK : lDg ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lDi : lbK ≠ lDi := by decide
@[simp] theorem lb_lDi_ne_lbK : lDi ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lRp : lbK ≠ lRp := by decide
@[simp] theorem lb_lRp_ne_lbK : lRp ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lRn : lbK ≠ lRn := by decide
@[simp] theorem lb_lRn_ne_lbK : lRn ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lFle : lbK ≠ lFle := by decide
@[simp] theorem lb_lFle_ne_lbK : lFle ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lDir : lbK ≠ lDir := by decide
@[simp] theorem lb_lDir_ne_lbK : lDir ≠ lbK := by decide
@[simp] theorem lb_lbK_ne_lKb : lbK ≠ lKb := by decide
@[simp] theorem lb_lKb_ne_lbK : lKb ≠ lbK := by decide
@[simp] theorem lb_lbH_ne_lbK : lbH ≠ lbK := by decide
@[simp] theorem lb_lbH_ne_lbB : lbH ≠ lbB := by decide
@[simp] theorem lb_lbH_ne_lbR : lbH ≠ lbR := by decide
@[simp] theorem lb_lbH_ne_lFl : lbH ≠ lFl := by decide
@[simp] theorem lb_lFl_ne_lbH : lFl ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lDh : lbH ≠ lDh := by decide
@[simp] theorem lb_lDh_ne_lbH : lDh ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lDt : lbH ≠ lDt := by decide
@[simp] theorem lb_lDt_ne_lbH : lDt ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lDg : lbH ≠ lDg := by decide
@[simp] theorem lb_lDg_ne_lbH : lDg ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lDi : lbH ≠ lDi := by decide
@[simp] theorem lb_lDi_ne_lbH : lDi ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lRp : lbH ≠ lRp := by decide
@[simp] theorem lb_lRp_ne_lbH : lRp ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lRn : lbH ≠ lRn := by decide
@[simp] theorem lb_lRn_ne_lbH : lRn ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lFle : lbH ≠ lFle := by decide
@[simp] theorem lb_lFle_ne_lbH : lFle ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lDir : lbH ≠ lDir := by decide
@[simp] theorem lb_lDir_ne_lbH : lDir ≠ lbH := by decide
@[simp] theorem lb_lbH_ne_lKb : lbH ≠ lKb := by decide
@[simp] theorem lb_lKb_ne_lbH : lKb ≠ lbH := by decide
@[simp] theorem lb_lbB_ne_lbK : lbB ≠ lbK := by decide
@[simp] theorem lb_lbB_ne_lbH : lbB ≠ lbH := by decide
@[simp] theorem lb_lbB_ne_lbR : lbB ≠ lbR := by decide
@[simp] theorem lb_lbB_ne_lFl : lbB ≠ lFl := by decide
@[simp] theorem lb_lFl_ne_lbB : lFl ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lDh : lbB ≠ lDh := by decide
@[simp] theorem lb_lDh_ne_lbB : lDh ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lDt : lbB ≠ lDt := by decide
@[simp] theorem lb_lDt_ne_lbB : lDt ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lDg : lbB ≠ lDg := by decide
@[simp] theorem lb_lDg_ne_lbB : lDg ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lDi : lbB ≠ lDi := by decide
@[simp] theorem lb_lDi_ne_lbB : lDi ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lRp : lbB ≠ lRp := by decide
@[simp] theorem lb_lRp_ne_lbB : lRp ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lRn : lbB ≠ lRn := by decide
@[simp] theorem lb_lRn_ne_lbB : lRn ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lFle : lbB ≠ lFle := by decide
@[simp] theorem lb_lFle_ne_lbB : lFle ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lDir : lbB ≠ lDir := by decide
@[simp] theorem lb_lDir_ne_lbB : lDir ≠ lbB := by decide
@[simp] theorem lb_lbB_ne_lKb : lbB ≠ lKb := by decide
@[simp] theorem lb_lKb_ne_lbB : lKb ≠ lbB := by decide
@[simp] theorem lb_lbR_ne_lbK : lbR ≠ lbK := by decide
@[simp] theorem lb_lbR_ne_lbH : lbR ≠ lbH := by decide
@[simp] theorem lb_lbR_ne_lbB : lbR ≠ lbB := by decide
@[simp] theorem lb_lbR_ne_lFl : lbR ≠ lFl := by decide
@[simp] theorem lb_lFl_ne_lbR : lFl ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lDh : lbR ≠ lDh := by decide
@[simp] theorem lb_lDh_ne_lbR : lDh ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lDt : lbR ≠ lDt := by decide
@[simp] theorem lb_lDt_ne_lbR : lDt ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lDg : lbR ≠ lDg := by decide
@[simp] theorem lb_lDg_ne_lbR : lDg ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lDi : lbR ≠ lDi := by decide
@[simp] theorem lb_lDi_ne_lbR : lDi ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lRp : lbR ≠ lRp := by decide
@[simp] theorem lb_lRp_ne_lbR : lRp ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lRn : lbR ≠ lRn := by decide
@[simp] theorem lb_lRn_ne_lbR : lRn ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lFle : lbR ≠ lFle := by decide
@[simp] theorem lb_lFle_ne_lbR : lFle ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lDir : lbR ≠ lDir := by decide
@[simp] theorem lb_lDir_ne_lbR : lDir ≠ lbR := by decide
@[simp] theorem lb_lbR_ne_lKb : lbR ≠ lKb := by decide
@[simp] theorem lb_lKb_ne_lbR : lKb ≠ lbR := by decide

def lbParams : List MlS := [lbK, lbH]
def lbLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lbB, lbR]

def lbCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv lbK) (.const 0))
    (.return (vv lbH))
    (.ite (tagIsE lbH 5)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv lbH)) (.seq eViewP
      (.seq (.assign .local lbB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, lbR), none)) fLb [.op .sub [vv lbK, .const 1], vv lbB])
        (.return (vv lbR)))))))
      (.return (vv lbH)))

def lbBody : ProgHOL 64 := prologue lbLocals lbCore

section
variable {σ : Type}

theorem lb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lbLocals → (ctxEnv C ++ lbParams.zip vals).get x = none :=
  Knot.params_none C lbLocals lbParams vals (by decide) (by decide)

theorem lb_spec (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fLb = some (lbParams.map (fun p => (p, ShapeHOL.one)), lbBody, .one)) :
    ∀ k (h : EIdx) (s : AState), k < 2 ^ 64 →
      SpecR (σ := σ) (Pre C s (lbParams.zip [BitVec.ofNat 64 k, Enc.idxW h])) lbBody s (lamBody k h) (PostK C) := by
  intro k
  induction k with
  | zero =>
    intro h s _
    refine specR_prologue (Knot.postK_locals C) (lb_none C _) ?_
    unfold lbCore
    rw [lamBody]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (Enc.idxW h) (by simp +decide [Env.get, lbParams, ctxEnv])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro h s hk
    refine specR_prologue (Knot.postK_locals C) (lb_none C _) ?_
    unfold lbCore
    rw [lamBody]
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV lbH h 5 (by decide) (by decide) (by simp +decide [Env.get, lbParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [ite_eq_left (show (h.tag == ETag.lam) = true by simp [htg, ETag.lam])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
      refine specR_assignI lDh (vv lbH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, lbParams, ctxEnv]) ?_
      refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v P hv htn _ => ?_)
      have h5 : v.tagN = 5 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .lam ty b := by
        cases v <;> simp [ENodeView.tagN] at h5 ⊢
      have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      refine specR_loadI' lbB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := lamBody k b >>= fun r => pure r) (by simp) ?_
      refine specR_callKH lbR fLb lbParams [.op .sub [vv lbK, .const 1], vv lbB] lbBody
        [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcl
        ⟨by simp +decide [sev, Env.get, lbParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (ih b s (by omega)) (fun r s' H' hp => ?_)
      exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [ite_eq_right (show ¬ (h.tag == ETag.lam) = true by simpa [ETag.lam] using htg)]
      exact specR_returnI _ (Enc.idxW h) (by simp +decide [Env.get, lbParams, ctxEnv])
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
