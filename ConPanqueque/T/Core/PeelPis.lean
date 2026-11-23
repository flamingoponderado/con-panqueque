import ConPanqueque.T.Core.StepApp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `peelPis`: the residual after `k` syntactic ∀ binders

A recursive function over `k`: `k = 0` answers `some h`; a `forallE` handle recurses on its body; anything
else answers `none`. The answer is `optW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem viewBind_of_view_forallE {st : EStore} {i ty b : EIdx}
    (htg : i.tag = ETag.forallE) (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  cases hc : st.viewBind i with
  | some p =>
    obtain ⟨ty', b'⟩ := p
    have := ConRon.Bridge.view_of_viewBind_forallE htg hc
    rw [h] at this; cases this; rfl
  | none =>
    exfalso
    revert h hc
    simp only [EStore.view, EStore.viewBind, EStore.persGetBind]
    split <;> [skip; split] <;> simp [ETables.get, ETables.getBind, htg] <;>
      (simp only [show ETag.forallE ≠ ETag.bvar by decide, show ETag.forallE ≠ ETag.fvar by decide,
        show ETag.forallE ≠ ETag.sort by decide, show ETag.forallE ≠ ETag.const by decide,
        show ETag.forallE ≠ ETag.app by decide, show ETag.forallE ≠ ETag.lam by decide, ite_false];
        intro h1 h2; rw [Option.map_eq_none_iff] at h2; rw [h2] at h1; simp at h1)

def pK := ofString "ppk"
def pH := ofString "pph"
def pB := ofString "ppb"
def pR := ofString "ppr"
def fPp := ofString "peelPis"

@[simp] theorem pp_pK_ne_pH : pK ≠ pH := by decide
@[simp] theorem pp_pK_ne_pB : pK ≠ pB := by decide
@[simp] theorem pp_pK_ne_pR : pK ≠ pR := by decide
@[simp] theorem pp_pK_ne_lFl : pK ≠ lFl := by decide
@[simp] theorem pp_lFl_ne_pK : lFl ≠ pK := by decide
@[simp] theorem pp_pK_ne_lDh : pK ≠ lDh := by decide
@[simp] theorem pp_lDh_ne_pK : lDh ≠ pK := by decide
@[simp] theorem pp_pK_ne_lDt : pK ≠ lDt := by decide
@[simp] theorem pp_lDt_ne_pK : lDt ≠ pK := by decide
@[simp] theorem pp_pK_ne_lDg : pK ≠ lDg := by decide
@[simp] theorem pp_lDg_ne_pK : lDg ≠ pK := by decide
@[simp] theorem pp_pK_ne_lDi : pK ≠ lDi := by decide
@[simp] theorem pp_lDi_ne_pK : lDi ≠ pK := by decide
@[simp] theorem pp_pK_ne_lRp : pK ≠ lRp := by decide
@[simp] theorem pp_lRp_ne_pK : lRp ≠ pK := by decide
@[simp] theorem pp_pK_ne_lRn : pK ≠ lRn := by decide
@[simp] theorem pp_lRn_ne_pK : lRn ≠ pK := by decide
@[simp] theorem pp_pK_ne_lFle : pK ≠ lFle := by decide
@[simp] theorem pp_lFle_ne_pK : lFle ≠ pK := by decide
@[simp] theorem pp_pK_ne_lDir : pK ≠ lDir := by decide
@[simp] theorem pp_lDir_ne_pK : lDir ≠ pK := by decide
@[simp] theorem pp_pK_ne_lKb : pK ≠ lKb := by decide
@[simp] theorem pp_lKb_ne_pK : lKb ≠ pK := by decide
@[simp] theorem pp_pH_ne_pK : pH ≠ pK := by decide
@[simp] theorem pp_pH_ne_pB : pH ≠ pB := by decide
@[simp] theorem pp_pH_ne_pR : pH ≠ pR := by decide
@[simp] theorem pp_pH_ne_lFl : pH ≠ lFl := by decide
@[simp] theorem pp_lFl_ne_pH : lFl ≠ pH := by decide
@[simp] theorem pp_pH_ne_lDh : pH ≠ lDh := by decide
@[simp] theorem pp_lDh_ne_pH : lDh ≠ pH := by decide
@[simp] theorem pp_pH_ne_lDt : pH ≠ lDt := by decide
@[simp] theorem pp_lDt_ne_pH : lDt ≠ pH := by decide
@[simp] theorem pp_pH_ne_lDg : pH ≠ lDg := by decide
@[simp] theorem pp_lDg_ne_pH : lDg ≠ pH := by decide
@[simp] theorem pp_pH_ne_lDi : pH ≠ lDi := by decide
@[simp] theorem pp_lDi_ne_pH : lDi ≠ pH := by decide
@[simp] theorem pp_pH_ne_lRp : pH ≠ lRp := by decide
@[simp] theorem pp_lRp_ne_pH : lRp ≠ pH := by decide
@[simp] theorem pp_pH_ne_lRn : pH ≠ lRn := by decide
@[simp] theorem pp_lRn_ne_pH : lRn ≠ pH := by decide
@[simp] theorem pp_pH_ne_lFle : pH ≠ lFle := by decide
@[simp] theorem pp_lFle_ne_pH : lFle ≠ pH := by decide
@[simp] theorem pp_pH_ne_lDir : pH ≠ lDir := by decide
@[simp] theorem pp_lDir_ne_pH : lDir ≠ pH := by decide
@[simp] theorem pp_pH_ne_lKb : pH ≠ lKb := by decide
@[simp] theorem pp_lKb_ne_pH : lKb ≠ pH := by decide
@[simp] theorem pp_pB_ne_pK : pB ≠ pK := by decide
@[simp] theorem pp_pB_ne_pH : pB ≠ pH := by decide
@[simp] theorem pp_pB_ne_pR : pB ≠ pR := by decide
@[simp] theorem pp_pB_ne_lFl : pB ≠ lFl := by decide
@[simp] theorem pp_lFl_ne_pB : lFl ≠ pB := by decide
@[simp] theorem pp_pB_ne_lDh : pB ≠ lDh := by decide
@[simp] theorem pp_lDh_ne_pB : lDh ≠ pB := by decide
@[simp] theorem pp_pB_ne_lDt : pB ≠ lDt := by decide
@[simp] theorem pp_lDt_ne_pB : lDt ≠ pB := by decide
@[simp] theorem pp_pB_ne_lDg : pB ≠ lDg := by decide
@[simp] theorem pp_lDg_ne_pB : lDg ≠ pB := by decide
@[simp] theorem pp_pB_ne_lDi : pB ≠ lDi := by decide
@[simp] theorem pp_lDi_ne_pB : lDi ≠ pB := by decide
@[simp] theorem pp_pB_ne_lRp : pB ≠ lRp := by decide
@[simp] theorem pp_lRp_ne_pB : lRp ≠ pB := by decide
@[simp] theorem pp_pB_ne_lRn : pB ≠ lRn := by decide
@[simp] theorem pp_lRn_ne_pB : lRn ≠ pB := by decide
@[simp] theorem pp_pB_ne_lFle : pB ≠ lFle := by decide
@[simp] theorem pp_lFle_ne_pB : lFle ≠ pB := by decide
@[simp] theorem pp_pB_ne_lDir : pB ≠ lDir := by decide
@[simp] theorem pp_lDir_ne_pB : lDir ≠ pB := by decide
@[simp] theorem pp_pB_ne_lKb : pB ≠ lKb := by decide
@[simp] theorem pp_lKb_ne_pB : lKb ≠ pB := by decide
@[simp] theorem pp_pR_ne_pK : pR ≠ pK := by decide
@[simp] theorem pp_pR_ne_pH : pR ≠ pH := by decide
@[simp] theorem pp_pR_ne_pB : pR ≠ pB := by decide
@[simp] theorem pp_pR_ne_lFl : pR ≠ lFl := by decide
@[simp] theorem pp_lFl_ne_pR : lFl ≠ pR := by decide
@[simp] theorem pp_pR_ne_lDh : pR ≠ lDh := by decide
@[simp] theorem pp_lDh_ne_pR : lDh ≠ pR := by decide
@[simp] theorem pp_pR_ne_lDt : pR ≠ lDt := by decide
@[simp] theorem pp_lDt_ne_pR : lDt ≠ pR := by decide
@[simp] theorem pp_pR_ne_lDg : pR ≠ lDg := by decide
@[simp] theorem pp_lDg_ne_pR : lDg ≠ pR := by decide
@[simp] theorem pp_pR_ne_lDi : pR ≠ lDi := by decide
@[simp] theorem pp_lDi_ne_pR : lDi ≠ pR := by decide
@[simp] theorem pp_pR_ne_lRp : pR ≠ lRp := by decide
@[simp] theorem pp_lRp_ne_pR : lRp ≠ pR := by decide
@[simp] theorem pp_pR_ne_lRn : pR ≠ lRn := by decide
@[simp] theorem pp_lRn_ne_pR : lRn ≠ pR := by decide
@[simp] theorem pp_pR_ne_lFle : pR ≠ lFle := by decide
@[simp] theorem pp_lFle_ne_pR : lFle ≠ pR := by decide
@[simp] theorem pp_pR_ne_lDir : pR ≠ lDir := by decide
@[simp] theorem pp_lDir_ne_pR : lDir ≠ pR := by decide
@[simp] theorem pp_pR_ne_lKb : pR ≠ lKb := by decide
@[simp] theorem pp_lKb_ne_pR : lKb ≠ pR := by decide

def ppParams : List MlS := [pK, pH]
def ppLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pB, pR]

def ppCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pK) (.const 0))
    (.return (.op .add [vv pH, .const 1]))
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local pB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, pR), none)) fPp [.op .sub [vv pK, .const 1], vv pB])
        (.return (vv pR)))))))
      (.return (.const 0)))

def ppBody : ProgHOL 64 := prologue ppLocals ppCore

section
variable {σ : Type}

theorem pp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ppLocals → (ctxEnv C ++ ppParams.zip vals).get x = none :=
  Knot.params_none C ppLocals ppParams vals (by decide) (by decide)

/-- Call an `optW` function whose spec is `UD.PostO`, then return its answer. -/
theorem specR_callO {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM (Option EIdx)}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (σ := σ) (Pre C s (ps.zip vs)) Bd s m (UD.PostO C)) :
    SpecR (σ := σ) (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) (.return (vv x))) s m
      (UD.PostO C) := by
  refine specR_congr (m' := m >>= fun st => pure st) (by simp) ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes (UD.PostO C) (fun o w _ _ => w = optW o)
    (fun o w s' t' ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec)
    (fun o w s' H' hp hw => ?_)
  subst hw
  exact specR_returnI _ (optW o) (by simp) (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem pp_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fPp = some (ppParams.map (fun p => (p, ShapeHOL.one)), ppBody, .one)) :
    ∀ k (h : EIdx) (s : AState), k < 2 ^ 64 →
      SpecR (σ := σ) (Pre C s (ppParams.zip [BitVec.ofNat 64 k, Enc.idxW h])) ppBody s (peelPis k h) (UD.PostO C) := by
  intro k
  induction k with
  | zero =>
    intro h s _
    refine specR_prologue (UD.postO_locals C) (pp_none C _) ?_
    unfold ppCore
    rw [peelPis]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ppParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (optW (some h)) (by simp +decide [sev, Env.get, ppParams, ctxEnv, optWG])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro h s hk
    refine specR_prologue (UD.postO_locals C) (pp_none C _) ?_
    unfold ppCore
    rw [peelPis]
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ppParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV pH h 6 (by decide) (by decide) (by simp +decide [Env.get, ppParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ppParams, ctxEnv]) ?_
      refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
        cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      refine specR_loadI' pB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      exact specR_callO pR fPp ppParams [.op .sub [vv pK, .const 1], vv pB] ppBody
        [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcp
        ⟨by simp +decide [sev, Env.get, ppParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (ih b s (by omega))
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `projCert`: the constructor's stored type has the spine's arity -/

def qC := ofString "pcc"
def qK := ofString "pcn"
def qW := ofString "pcw"
def qQ := ofString "pcq"
def qT := ofString "pct"
def qY := ofString "pcy"
def qZ := ofString "pcr"
def fPc := ofString "projCert"

@[simp] theorem pc_qC_ne_qN : qC ≠ qK := by decide
@[simp] theorem pc_qC_ne_qW : qC ≠ qW := by decide
@[simp] theorem pc_qC_ne_qQ : qC ≠ qQ := by decide
@[simp] theorem pc_qC_ne_qT : qC ≠ qT := by decide
@[simp] theorem pc_qC_ne_qY : qC ≠ qY := by decide
@[simp] theorem pc_qC_ne_qR : qC ≠ qZ := by decide
@[simp] theorem pc_qC_ne_lKb : qC ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qC : lKb ≠ qC := by decide
@[simp] theorem pc_qN_ne_qC : qK ≠ qC := by decide
@[simp] theorem pc_qN_ne_qW : qK ≠ qW := by decide
@[simp] theorem pc_qN_ne_qQ : qK ≠ qQ := by decide
@[simp] theorem pc_qN_ne_qT : qK ≠ qT := by decide
@[simp] theorem pc_qN_ne_qY : qK ≠ qY := by decide
@[simp] theorem pc_qN_ne_qR : qK ≠ qZ := by decide
@[simp] theorem pc_qN_ne_lKb : qK ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qN : lKb ≠ qK := by decide
@[simp] theorem pc_qW_ne_qC : qW ≠ qC := by decide
@[simp] theorem pc_qW_ne_qN : qW ≠ qK := by decide
@[simp] theorem pc_qW_ne_qQ : qW ≠ qQ := by decide
@[simp] theorem pc_qW_ne_qT : qW ≠ qT := by decide
@[simp] theorem pc_qW_ne_qY : qW ≠ qY := by decide
@[simp] theorem pc_qW_ne_qR : qW ≠ qZ := by decide
@[simp] theorem pc_qW_ne_lKb : qW ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qW : lKb ≠ qW := by decide
@[simp] theorem pc_qQ_ne_qC : qQ ≠ qC := by decide
@[simp] theorem pc_qQ_ne_qN : qQ ≠ qK := by decide
@[simp] theorem pc_qQ_ne_qW : qQ ≠ qW := by decide
@[simp] theorem pc_qQ_ne_qT : qQ ≠ qT := by decide
@[simp] theorem pc_qQ_ne_qY : qQ ≠ qY := by decide
@[simp] theorem pc_qQ_ne_qR : qQ ≠ qZ := by decide
@[simp] theorem pc_qQ_ne_lKb : qQ ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qQ : lKb ≠ qQ := by decide
@[simp] theorem pc_qT_ne_qC : qT ≠ qC := by decide
@[simp] theorem pc_qT_ne_qN : qT ≠ qK := by decide
@[simp] theorem pc_qT_ne_qW : qT ≠ qW := by decide
@[simp] theorem pc_qT_ne_qQ : qT ≠ qQ := by decide
@[simp] theorem pc_qT_ne_qY : qT ≠ qY := by decide
@[simp] theorem pc_qT_ne_qR : qT ≠ qZ := by decide
@[simp] theorem pc_qT_ne_lKb : qT ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qT : lKb ≠ qT := by decide
@[simp] theorem pc_qY_ne_qC : qY ≠ qC := by decide
@[simp] theorem pc_qY_ne_qN : qY ≠ qK := by decide
@[simp] theorem pc_qY_ne_qW : qY ≠ qW := by decide
@[simp] theorem pc_qY_ne_qQ : qY ≠ qQ := by decide
@[simp] theorem pc_qY_ne_qT : qY ≠ qT := by decide
@[simp] theorem pc_qY_ne_qR : qY ≠ qZ := by decide
@[simp] theorem pc_qY_ne_lKb : qY ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qY : lKb ≠ qY := by decide
@[simp] theorem pc_qR_ne_qC : qZ ≠ qC := by decide
@[simp] theorem pc_qR_ne_qN : qZ ≠ qK := by decide
@[simp] theorem pc_qR_ne_qW : qZ ≠ qW := by decide
@[simp] theorem pc_qR_ne_qQ : qZ ≠ qQ := by decide
@[simp] theorem pc_qR_ne_qT : qZ ≠ qT := by decide
@[simp] theorem pc_qR_ne_qY : qZ ≠ qY := by decide
@[simp] theorem pc_qR_ne_lKb : qZ ≠ lKb := by decide
@[simp] theorem pc_lKb_ne_qR : lKb ≠ qZ := by decide

def pcParams : List MlS := [qC, qK]
def pcLocals : List MlS := [qW, qQ, qT, qY, qZ]

def pcCore (C : Ctx) : ProgHOL 64 :=
  envFindP C qW (vv qC)
  (.ite (.cmp .equal (vv qW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local qQ (.op .sub [vv qW, .const 1])) (.seq (.assign .local qT (.load .one (vv qQ)))
  (.ite (.cmp .notEqual (vv qT) (.const 4)) (.return (.const 0))
  (.seq (.assign .local qY (.load .one (.op .add [vv qQ, .const 24])))
  (.seq (.call (some (some (.local, qZ), none)) fPp [vv qK, vv qY])
    (.return (.cmp .notEqual (vv qZ) (.const 0)))))))))

def pcBody (C : Ctx) : ProgHOL 64 := prologue pcLocals (pcCore C)

section
variable {σ : Type}

theorem pc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pcLocals → (ctxEnv C ++ pcParams.zip vals).get x = none :=
  Knot.params_none C pcLocals pcParams vals (by decide) (by decide)

theorem ecell_add24 (C : Ctx) (o : Nat) : ecell C o + 24 = ecell C (o + 3) := by
  rw [show (24 : BitVec 64) = BitVec.ofNat 64 (8 * 3) from rfl, ecell_add]

theorem pc_spec (C : Ctx) (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcp : C.code.lookup fPp = some (ppParams.map (fun p => (p, ShapeHOL.one)), ppBody, .one))
    (c : NIdx) (args : List EIdx) (s : AState) (hl : args.length < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (pcParams.zip [Enc.idxW c, BitVec.ofNat 64 args.length])) (pcBody C) s
      (projCert C.fe c args) (Knot.PostB C) := by
  refine specR_prologue (Knot.postB_locals C) (pc_none C _) ?_
  unfold pcCore projCert
  refine specR_envFindI hok hcodeG hcodeP qW (vv qC) c (by decide) (by simp +decide [Env.get, pcParams, ctxEnv])
    (by simp +decide [Env.get, pcParams, ctxEnv]) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI qQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  refine specR_envLoadI qT (vv qQ) o _ (by decide) (by simp) (UD.cie_tag hci) ?_
  cases ci
  case ctorInfo cv np nf ind =>
    dsimp only
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hty : C.EH[o + 3]? = some (Enc.idxW cv.type) := by
      have := hci.1.2.2; simpa [IConstantInfo.toConstantVal] using this
    refine specR_envLoadI qY (.op .add [vv qQ, .const 24]) (o + 3) _ (by decide)
      (by simp [sev, vv]; exact ecell_add24 C o) hty ?_
    unfold teleArityOk
    refine specR_callNIH qZ fPp ppParams [vv qK, vv qY] ppBody [BitVec.ofNat 64 args.length, Enc.idxW cv.type]
      (by decide) rfl (by decide) hcp ⟨by simp +decide [Env.get, pcParams, ctxEnv], by simp, trivial⟩
      (UD.PostO C) (fun o w _ _ => w = optW o) (fun o w s' t' ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ppParams _ rfl hlk) (pp_spec C hok hcp _ _ s hl))
      (fun r w s' H' hp hw => ?_)
    subst hw
    refine specR_returnI _ (boolW r.isSome) ?_ (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases r with
    | none => simp [sev, optWG, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    | some e => simp [sev, optWG, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne e
  all_goals
    dsimp only
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
