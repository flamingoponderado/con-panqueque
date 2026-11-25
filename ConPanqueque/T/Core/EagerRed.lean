import ConPanqueque.T.Core.InferLamsLoop
import ConPanqueque.T.PinRead
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `isEagerReduce`

Is a handle `eagerReduce _ _`: two `app` views, then the head's `const` view, its name compared with the
`eagerReduce` pin.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ieH := ofString "ien_h"
def ieF := ofString "ien_f"
def ieG := ofString "ien_g"
def ieC := ofString "ien_c"
def ieP := ofString "ien_p"
def fIe := ofString "isEagerReduce"

@[simp] theorem ie_ieH_ne_ieF : ieH ≠ ieF := by decide
@[simp] theorem ie_ieH_ne_ieG : ieH ≠ ieG := by decide
@[simp] theorem ie_ieH_ne_ieC : ieH ≠ ieC := by decide
@[simp] theorem ie_ieH_ne_ieP : ieH ≠ ieP := by decide
@[simp] theorem ie_ieH_ne_lFl : ieH ≠ lFl := by decide
@[simp] theorem ie_lFl_ne_ieH : lFl ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lDh : ieH ≠ lDh := by decide
@[simp] theorem ie_lDh_ne_ieH : lDh ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lDt : ieH ≠ lDt := by decide
@[simp] theorem ie_lDt_ne_ieH : lDt ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lDg : ieH ≠ lDg := by decide
@[simp] theorem ie_lDg_ne_ieH : lDg ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lDi : ieH ≠ lDi := by decide
@[simp] theorem ie_lDi_ne_ieH : lDi ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lRp : ieH ≠ lRp := by decide
@[simp] theorem ie_lRp_ne_ieH : lRp ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lRn : ieH ≠ lRn := by decide
@[simp] theorem ie_lRn_ne_ieH : lRn ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lDir : ieH ≠ lDir := by decide
@[simp] theorem ie_lDir_ne_ieH : lDir ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lFle : ieH ≠ lFle := by decide
@[simp] theorem ie_lFle_ne_ieH : lFle ≠ ieH := by decide
@[simp] theorem ie_ieH_ne_lKb : ieH ≠ lKb := by decide
@[simp] theorem ie_lKb_ne_ieH : lKb ≠ ieH := by decide
@[simp] theorem ie_ieF_ne_ieH : ieF ≠ ieH := by decide
@[simp] theorem ie_ieF_ne_ieG : ieF ≠ ieG := by decide
@[simp] theorem ie_ieF_ne_ieC : ieF ≠ ieC := by decide
@[simp] theorem ie_ieF_ne_ieP : ieF ≠ ieP := by decide
@[simp] theorem ie_ieF_ne_lFl : ieF ≠ lFl := by decide
@[simp] theorem ie_lFl_ne_ieF : lFl ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lDh : ieF ≠ lDh := by decide
@[simp] theorem ie_lDh_ne_ieF : lDh ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lDt : ieF ≠ lDt := by decide
@[simp] theorem ie_lDt_ne_ieF : lDt ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lDg : ieF ≠ lDg := by decide
@[simp] theorem ie_lDg_ne_ieF : lDg ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lDi : ieF ≠ lDi := by decide
@[simp] theorem ie_lDi_ne_ieF : lDi ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lRp : ieF ≠ lRp := by decide
@[simp] theorem ie_lRp_ne_ieF : lRp ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lRn : ieF ≠ lRn := by decide
@[simp] theorem ie_lRn_ne_ieF : lRn ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lDir : ieF ≠ lDir := by decide
@[simp] theorem ie_lDir_ne_ieF : lDir ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lFle : ieF ≠ lFle := by decide
@[simp] theorem ie_lFle_ne_ieF : lFle ≠ ieF := by decide
@[simp] theorem ie_ieF_ne_lKb : ieF ≠ lKb := by decide
@[simp] theorem ie_lKb_ne_ieF : lKb ≠ ieF := by decide
@[simp] theorem ie_ieG_ne_ieH : ieG ≠ ieH := by decide
@[simp] theorem ie_ieG_ne_ieF : ieG ≠ ieF := by decide
@[simp] theorem ie_ieG_ne_ieC : ieG ≠ ieC := by decide
@[simp] theorem ie_ieG_ne_ieP : ieG ≠ ieP := by decide
@[simp] theorem ie_ieG_ne_lFl : ieG ≠ lFl := by decide
@[simp] theorem ie_lFl_ne_ieG : lFl ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lDh : ieG ≠ lDh := by decide
@[simp] theorem ie_lDh_ne_ieG : lDh ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lDt : ieG ≠ lDt := by decide
@[simp] theorem ie_lDt_ne_ieG : lDt ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lDg : ieG ≠ lDg := by decide
@[simp] theorem ie_lDg_ne_ieG : lDg ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lDi : ieG ≠ lDi := by decide
@[simp] theorem ie_lDi_ne_ieG : lDi ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lRp : ieG ≠ lRp := by decide
@[simp] theorem ie_lRp_ne_ieG : lRp ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lRn : ieG ≠ lRn := by decide
@[simp] theorem ie_lRn_ne_ieG : lRn ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lDir : ieG ≠ lDir := by decide
@[simp] theorem ie_lDir_ne_ieG : lDir ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lFle : ieG ≠ lFle := by decide
@[simp] theorem ie_lFle_ne_ieG : lFle ≠ ieG := by decide
@[simp] theorem ie_ieG_ne_lKb : ieG ≠ lKb := by decide
@[simp] theorem ie_lKb_ne_ieG : lKb ≠ ieG := by decide
@[simp] theorem ie_ieC_ne_ieH : ieC ≠ ieH := by decide
@[simp] theorem ie_ieC_ne_ieF : ieC ≠ ieF := by decide
@[simp] theorem ie_ieC_ne_ieG : ieC ≠ ieG := by decide
@[simp] theorem ie_ieC_ne_ieP : ieC ≠ ieP := by decide
@[simp] theorem ie_ieC_ne_lFl : ieC ≠ lFl := by decide
@[simp] theorem ie_lFl_ne_ieC : lFl ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lDh : ieC ≠ lDh := by decide
@[simp] theorem ie_lDh_ne_ieC : lDh ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lDt : ieC ≠ lDt := by decide
@[simp] theorem ie_lDt_ne_ieC : lDt ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lDg : ieC ≠ lDg := by decide
@[simp] theorem ie_lDg_ne_ieC : lDg ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lDi : ieC ≠ lDi := by decide
@[simp] theorem ie_lDi_ne_ieC : lDi ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lRp : ieC ≠ lRp := by decide
@[simp] theorem ie_lRp_ne_ieC : lRp ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lRn : ieC ≠ lRn := by decide
@[simp] theorem ie_lRn_ne_ieC : lRn ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lDir : ieC ≠ lDir := by decide
@[simp] theorem ie_lDir_ne_ieC : lDir ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lFle : ieC ≠ lFle := by decide
@[simp] theorem ie_lFle_ne_ieC : lFle ≠ ieC := by decide
@[simp] theorem ie_ieC_ne_lKb : ieC ≠ lKb := by decide
@[simp] theorem ie_lKb_ne_ieC : lKb ≠ ieC := by decide
@[simp] theorem ie_ieP_ne_ieH : ieP ≠ ieH := by decide
@[simp] theorem ie_ieP_ne_ieF : ieP ≠ ieF := by decide
@[simp] theorem ie_ieP_ne_ieG : ieP ≠ ieG := by decide
@[simp] theorem ie_ieP_ne_ieC : ieP ≠ ieC := by decide
@[simp] theorem ie_ieP_ne_lFl : ieP ≠ lFl := by decide
@[simp] theorem ie_lFl_ne_ieP : lFl ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lDh : ieP ≠ lDh := by decide
@[simp] theorem ie_lDh_ne_ieP : lDh ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lDt : ieP ≠ lDt := by decide
@[simp] theorem ie_lDt_ne_ieP : lDt ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lDg : ieP ≠ lDg := by decide
@[simp] theorem ie_lDg_ne_ieP : lDg ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lDi : ieP ≠ lDi := by decide
@[simp] theorem ie_lDi_ne_ieP : lDi ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lRp : ieP ≠ lRp := by decide
@[simp] theorem ie_lRp_ne_ieP : lRp ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lRn : ieP ≠ lRn := by decide
@[simp] theorem ie_lRn_ne_ieP : lRn ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lDir : ieP ≠ lDir := by decide
@[simp] theorem ie_lDir_ne_ieP : lDir ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lFle : ieP ≠ lFle := by decide
@[simp] theorem ie_lFle_ne_ieP : lFle ≠ ieP := by decide
@[simp] theorem ie_ieP_ne_lKb : ieP ≠ lKb := by decide
@[simp] theorem ie_lKb_ne_ieP : lKb ≠ ieP := by decide

def ieParams : List MlS := [ieH]
def ieLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ieF, ieG, ieC, ieP]

def ieCore (C : Ctx) : ProgHOL 64 :=
  .ite (tagIs4E ieH)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ieH)) (.seq eViewP
    (.seq (.assign .local ieF (.load .one (vv lRp)))
    (.ite (tagIs4E ieF)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ieF)) (.seq eViewP
      (.seq (.assign .local ieG (.load .one (vv lRp)))
      (.ite (tagIsE ieG 3)
        (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ieG)) (.seq eViewP
        (.seq (.assign .local ieC (.load .one (vv lRp)))
        (.seq (.assign .local ieP (.load .one (.const (ecell C (C.PO + PIN_EAGER_REDUCE)))))
          (.return (.cmp .equal (vv ieC) (vv ieP))))))))
        (.return (.const 0)))))))
      (.return (.const 0)))))))
    (.return (.const 0))

def ieBody (C : Ctx) : ProgHOL 64 := prologue ieLocals (ieCore C)

section
variable {σ : Type}

theorem specR_tag4IteE {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (h : EIdx)
    (hh : Γ.get x = some (Enc.idxW h))
    (h1 : h.tag = 4 → SpecR (Inv C s Γ M D) c1 s m R) (h2 : h.tag ≠ 4 → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (tagIs4E x) c1 c2) s m R := by
  obtain ⟨w, hw, hiff⟩ := sev_tagIs4 Γ x h hh
  exact specR_ifI _ w hw (fun e => h1 (hiff.mp e)) (fun e => h2 (fun t => (hiff.mpr t) e))

theorem ie_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ieLocals → (ctxEnv C ++ ieParams.zip vals).get x = none :=
  Knot.params_none C ieLocals ieParams vals (by decide) (by decide)

theorem ie_spec (C : Ctx) (hok : CtxOK C) (s : AState) (h : EIdx) :
    SpecR (σ := σ) (Pre C s (ieParams.zip [Enc.idxW h])) (ieBody C) s (isEagerReduce h) (PostB C) := by
  refine specR_prologue (postB_locals C) (ie_none C _) ?_
  unfold ieCore isEagerReduce
  have hno : ∀ {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv C s Γ M D) (.return (.const 0)) s (pure false) (PostB C) := fun {Γ M D} =>
    specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_tag4IteE ieH h (by simp +decide [Env.get, ieParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (h.tag == ETag.app) = true by simpa [ETag.app] using htg)]
    exact hno
  rw [ite_eq_left (show (h.tag == ETag.app) = true by simp [htg, ETag.app])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ieH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ieParams, ctxEnv]) ?_
  refine specR_viewAppI h htg (by simp) (by simp +decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun f a P => ?_)
  dsimp only
  refine specR_loadI' ieF _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_dropM ?_
  refine specR_tag4IteE ieF f (by simp) (fun htf => ?_) (fun htf => ?_)
  swap
  · rw [ite_eq_right (show ¬ (f.tag == ETag.app) = true by simpa [ETag.app] using htf)]
    exact hno
  rw [ite_eq_left (show (f.tag == ETag.app) = true by simp [htf, ETag.app])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ieF) (Enc.idxW f) (by decide) (by simp) ?_
  refine specR_viewAppI f htf (by simp) (by simp +decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun g b P2 => ?_)
  dsimp only
  refine specR_loadI' ieG _ (P2 + 0) P2 (Enc.idxW g) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_dropM ?_
  refine Knot.specR_tagIteV ieG g 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (g.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact hno
  rw [ite_eq_left (show (g.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ieG) (Enc.idxW g) (by decide) (by simp) ?_
  refine specR_viewP g (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P3 hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  have hvc : s.store.viewConst g = some (c, us) := viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' ieC (vv lRp) P3 (P3 + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P3 (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_dropM ?_
  unfold eagerReduceName pinEagerReduce
  refine specR_pinAtI hok PIN_EAGER_REDUCE (by decide) ieP (by decide) ?_
  refine specR_returnI _ (boolW (c == C.pins.names[PIN_EAGER_REDUCE]'(by rw [hok.pinsRel.1]; decide))) ?_
    (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  simp only [sev, sev_vv]
  simp
  by_cases he : c = C.pins.names[PIN_EAGER_REDUCE]'(by rw [hok.pinsRel.1]; decide)
  · rw [he]; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : Enc.idxW c ≠ Enc.idxW (C.pins.names[PIN_EAGER_REDUCE]'(by rw [hok.pinsRel.1]; decide)) :=
      fun x => he (Enc.idxW_inj x)
    simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, he]

end

end ConPanqueque.T.WC
