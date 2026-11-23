import ConPanqueque.T.Core.RescueAnd
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `formerResSort`: the sort a stored type's Π-telescope ends in

`piResult`, then a `sort` head's level (`optWG idxW`: the level plus one, or `0`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def fsT := ofString "fst"
def fsP := ofString "fsp"
def fsU := ofString "fsu"
def fFs := ofString "formerResSort"

@[simp] theorem fs_fsT_ne_fsP : fsT ≠ fsP := by decide
@[simp] theorem fs_fsT_ne_fsU : fsT ≠ fsU := by decide
@[simp] theorem fs_fsT_ne_lFl : fsT ≠ lFl := by decide
@[simp] theorem fs_lFl_ne_fsT : lFl ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lDh : fsT ≠ lDh := by decide
@[simp] theorem fs_lDh_ne_fsT : lDh ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lDt : fsT ≠ lDt := by decide
@[simp] theorem fs_lDt_ne_fsT : lDt ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lDg : fsT ≠ lDg := by decide
@[simp] theorem fs_lDg_ne_fsT : lDg ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lDi : fsT ≠ lDi := by decide
@[simp] theorem fs_lDi_ne_fsT : lDi ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lRp : fsT ≠ lRp := by decide
@[simp] theorem fs_lRp_ne_fsT : lRp ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lRn : fsT ≠ lRn := by decide
@[simp] theorem fs_lRn_ne_fsT : lRn ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lFle : fsT ≠ lFle := by decide
@[simp] theorem fs_lFle_ne_fsT : lFle ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lDir : fsT ≠ lDir := by decide
@[simp] theorem fs_lDir_ne_fsT : lDir ≠ fsT := by decide
@[simp] theorem fs_fsT_ne_lKb : fsT ≠ lKb := by decide
@[simp] theorem fs_lKb_ne_fsT : lKb ≠ fsT := by decide
@[simp] theorem fs_fsP_ne_fsT : fsP ≠ fsT := by decide
@[simp] theorem fs_fsP_ne_fsU : fsP ≠ fsU := by decide
@[simp] theorem fs_fsP_ne_lFl : fsP ≠ lFl := by decide
@[simp] theorem fs_lFl_ne_fsP : lFl ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lDh : fsP ≠ lDh := by decide
@[simp] theorem fs_lDh_ne_fsP : lDh ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lDt : fsP ≠ lDt := by decide
@[simp] theorem fs_lDt_ne_fsP : lDt ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lDg : fsP ≠ lDg := by decide
@[simp] theorem fs_lDg_ne_fsP : lDg ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lDi : fsP ≠ lDi := by decide
@[simp] theorem fs_lDi_ne_fsP : lDi ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lRp : fsP ≠ lRp := by decide
@[simp] theorem fs_lRp_ne_fsP : lRp ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lRn : fsP ≠ lRn := by decide
@[simp] theorem fs_lRn_ne_fsP : lRn ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lFle : fsP ≠ lFle := by decide
@[simp] theorem fs_lFle_ne_fsP : lFle ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lDir : fsP ≠ lDir := by decide
@[simp] theorem fs_lDir_ne_fsP : lDir ≠ fsP := by decide
@[simp] theorem fs_fsP_ne_lKb : fsP ≠ lKb := by decide
@[simp] theorem fs_lKb_ne_fsP : lKb ≠ fsP := by decide
@[simp] theorem fs_fsU_ne_fsT : fsU ≠ fsT := by decide
@[simp] theorem fs_fsU_ne_fsP : fsU ≠ fsP := by decide
@[simp] theorem fs_fsU_ne_lFl : fsU ≠ lFl := by decide
@[simp] theorem fs_lFl_ne_fsU : lFl ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lDh : fsU ≠ lDh := by decide
@[simp] theorem fs_lDh_ne_fsU : lDh ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lDt : fsU ≠ lDt := by decide
@[simp] theorem fs_lDt_ne_fsU : lDt ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lDg : fsU ≠ lDg := by decide
@[simp] theorem fs_lDg_ne_fsU : lDg ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lDi : fsU ≠ lDi := by decide
@[simp] theorem fs_lDi_ne_fsU : lDi ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lRp : fsU ≠ lRp := by decide
@[simp] theorem fs_lRp_ne_fsU : lRp ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lRn : fsU ≠ lRn := by decide
@[simp] theorem fs_lRn_ne_fsU : lRn ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lFle : fsU ≠ lFle := by decide
@[simp] theorem fs_lFle_ne_fsU : lFle ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lDir : fsU ≠ lDir := by decide
@[simp] theorem fs_lDir_ne_fsU : lDir ≠ fsU := by decide
@[simp] theorem fs_fsU_ne_lKb : fsU ≠ lKb := by decide
@[simp] theorem fs_lKb_ne_fsU : lKb ≠ fsU := by decide

def fsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, fsP, fsU]

def fsBody : ProgHOL 64 := prologue fsLocals
  (.seq (.call (some (some (.local, fsP), none)) ExM.fPir [.const (BitVec.ofNat 64 coreWalkFuel), vv fsT])
  (.ite (tagIsE fsP 2)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv fsP)) (.seq eViewP
    (.seq (.assign .local fsU (.load .one (vv lRp))) (.return (.op .add [vv fsU, .const 1]))))))
    (.return (.const 0))))

section
variable {σ : Type}

theorem fs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fsLocals → (ctxEnv C ++ [fsT].zip vals).get x = none :=
  Knot.params_none C fsLocals [fsT] vals (by decide) (by decide)

theorem viewSort_of_view {st : EStore} {i : EIdx} {u : LIdx}
    (htg : i.tag = ETag.sort) (h : st.view i = some (.sort u)) : st.viewSort i = some u := by
  cases hc : st.viewSort i with
  | some u' =>
    have := ConRon.Bridge.view_of_viewSort htg hc
    rw [h] at this; cases this; rfl
  | none =>
    exfalso
    revert h hc
    simp only [EStore.view, EStore.viewSort, EStore.persGetSort]
    split <;> [skip; split] <;> simp [ETables.get, ETables.getSort, htg] <;>
      (try simp only [show ETag.sort ≠ ETag.bvar by decide, show ETag.sort ≠ ETag.fvar by decide, ite_false]) <;>
      intro h1 h2 <;> (try rw [Option.map_eq_none_iff] at h2) <;> (try rw [h2] at h1) <;> simp at h1

theorem RO.piResult : ∀ (n : Nat) (h : EIdx), RO (ConRon.Arena.piResult n h)
  | 0, h => by rw [ConRon.Arena.piResult]; exact RO.fail _
  | n + 1, h => by
    rw [ConRon.Arena.piResult]
    refine RO.ite _ (RO.bind (RO.viewBind h) (fun o => ?_)) (RO.pure _)
    rcases o with _ | ⟨_, b⟩
    · exact RO.failDanglingE
    · exact RO.piResult n b

/-- An optional level answer: the level plus one, or `0` (the state is the one given). -/
def PostOL (C : Ctx) (s : AState) (o : Option LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = optWG Enc.idxW o ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s st

theorem fs_spec (C : Ctx) (hcp : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one))
    (s : AState) (ty : EIdx) :
    SpecR (σ := σ) (Pre C s [(fsT, Enc.idxW ty)]) fsBody s (formerResSort ty) (PostOL C s) := by
  refine specR_prologue (fun a w s' st L ⟨h1, h2, H', hp, h3⟩ => ⟨h1, h2, H', hp, sr_of_eq h3 rfl rfl rfl rfl⟩)
    (fs_none C [Enc.idxW ty]) ?_
  unfold formerResSort
  refine specR_callNIH fsP ExM.fPir [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv fsT] ExM.pirBody
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty] (by decide) rfl (by decide) hcp
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w s' st => piResult coreWalkFuel ty s = .ok (a, s') ∧ PostE C a w s' st)
    (fun a w s' _ => piResult coreWalkFuel ty s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hrun, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨hrun, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExM.pir_spec C hcp coreWalkFuel CV.coreWalkFuel_lt ty s)))
    (fun pr w s1 H1 hp1 ⟨hrun, hw⟩ => ?_)
  subst hw
  have hs1 : s1 = s := RO.piResult _ _ _ _ _ hrun
  subst s1
  refine Knot.specR_tagIteV fsP pr 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (pr.tag == ETag.sort) = true by simp [htg, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv fsP) (Enc.idxW pr) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H1) pr (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
    have hvs : s.store.viewSort pr = some u := viewSort_of_view (by rw [htg]; rfl) hv
    refine specR_runBind (show ConRon.Arena.viewSort pr s = .ok (some u, s) by
      show Except.ok (s.store.viewSort pr, s) = _; rw [hvs]) ?_
    dsimp only
    refine specR_loadI' fsU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    exact specR_returnI _ (optWG Enc.idxW (some u)) (by simp [sev, optWG])
      (fun t ht => ⟨rfl, rfl, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (pr.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_returnI _ (optWG Enc.idxW none) (by simp [optWG]; rfl)
      (fun t ht => ⟨rfl, rfl, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
