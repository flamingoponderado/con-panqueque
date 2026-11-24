import ConPanqueque.T.Decl.ConstsResolve
import ConPanqueque.T.Core.Wscoped
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `constsResolveF`: the memoized walk

Every constant a term mentions is in the environment: the DAG walk with a handle-keyed memo, the memo kept as a
memo list keyed `(handle, 0)`.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def crfF := ofString "crf_f"
def crfH := ofString "crf_h"
def crfM := ofString "crf_m"
def crfL := ofString "crf_l"
def crfR := ofString "crf_r"
def crfR2 := ofString "crf_r2"
def crfM2 := ofString "crf_m2"
def crfC1 := ofString "crf_c1"
def crfC2 := ofString "crf_c2"
def crfC3 := ofString "crf_c3"
def crfK1 := ofString "crf_k1"
def crfK2 := ofString "crf_k2"
def crfK3 := ofString "crf_k3"
def crfN := ofString "crf_n"
def crfO := ofString "crf_o"
def crfS := ofString "crf_s"
def crfY := ofString "crf_y"
def fCrf := ofString "constsResolveFGo"
def fCrl := ofString "constsResolveLeaf"

def crfParams : List MlS := [crfF, crfH, crfM]
def crfLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, crfL, crfR, crfR2, crfM2, crfC1, crfC2, crfC3,
  crfK1, crfK2, crfK3, crfN, crfO, crfS, crfY]

/-- The answer and the memo as a fresh pair block. -/
def crfRet (C : Ctx) (er em : ExpHOL 64) : ProgHOL 64 :=
  allocP C crfO (.const 16) (.seq (.store (vv crfO) er) (.seq (.store (.op .add [vv crfO, .const 8]) em)
    (.return (vv crfO))))

/-- Record the node's answer in the memo, then return. -/
def crfIns (C : Ctx) : ProgHOL 64 :=
  mlInsP C crfN (vv crfH) (.const 0) (vv crfR) (vv crfM2) (crfRet C (vv crfR) (vv crfN))

/-- One recursive call; its answer and memo read back. -/
def crfCall (k : MlS) (eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fCrf [.op .sub [vv crfF, .const 1], eH, eM])
  (.seq (.assign .local crfR (.load .one (vv k))) (.seq (.assign .local crfM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

def crfArm2 (C : Ctx) : ProgHOL 64 :=
  crfCall crfK1 (vv crfC1) (vv crfM) (.seq (.assign .local crfR2 (vv crfR))
    (crfCall crfK2 (vv crfC2) (vv crfM2) (.seq (.assign .local crfR (.op .and [vv crfR2, vv crfR])) (crfIns C))))

def crfArm3 (C : Ctx) : ProgHOL 64 :=
  crfCall crfK1 (vv crfC1) (vv crfM) (.seq (.assign .local crfR2 (vv crfR))
    (crfCall crfK2 (vv crfC2) (vv crfM2) (.seq (.assign .local crfR2 (.op .and [vv crfR2, vv crfR]))
      (crfCall crfK3 (vv crfC3) (vv crfM2) (.seq (.assign .local crfR (.op .and [vv crfR2, vv crfR])) (crfIns C))))))

def crfProj (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local crfS (.load .one (vv lRp)))
  (.seq (.assign .local crfC1 (.load .one (.op .add [vv lRp, .const 8])))
  (crfCall crfK1 (vv crfC1) (vv crfM)
    (envFindP C crfY (vv crfS)
      (.ite (.cmp .equal (vv crfY) (.const 0)) (.seq (.assign .local crfR (.const 0)) (crfIns C)) (crfIns C)))))

def crfCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv crfF) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv crfH)) (.seq eViewP
  (.ite (.op .or [.cmp .equal (vv lDg) (.const 0), .cmp .equal (vv lDg) (.const 2),
      .cmp .equal (vv lDg) (.const 3), .cmp .equal (vv lDg) (.const 8)])
    (.seq (.call (some (some (.local, crfR), none)) fCrl [vv crfH]) (crfRet C (vv crfR) (vv crfM)))
  (.seq (.call (some (some (.local, crfL), none)) fMl [vv crfM, vv crfH, .const 0])
  (.ite (.cmp .notEqual (vv crfL) (.const 0)) (crfRet C (.op .sub [vv crfL, .const 1]) (vv crfM))
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local crfC1 (.load .one (vv lRp))) (crfCall crfK1 (vv crfC1) (vv crfM) (crfIns C)))
  (.ite (.op .or [.cmp .equal (vv lDg) (.const 4), .cmp .equal (vv lDg) (.const 5), .cmp .equal (vv lDg) (.const 6)])
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8]))) (crfArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local crfC3 (.load .one (.op .add [vv lRp, .const 16]))) (crfArm3 C))))
    (crfProj C))))))))))

def crfBody (C : Ctx) : ProgHOL 64 := prologue crfLocals (crfCore C)

/-- A handle-keyed boolean memo, as a memo list. -/
def CrRep (C : Ctx) (H : List (BitVec 64)) (p : BitVec 64) (memo : Std.HashMap EIdx Bool) : Prop :=
  ∃ xs, MNodes C H p xs ∧ ∀ h : EIdx, memo[h]? = xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)

theorem crRep_empty (C : Ctx) (H : List (BitVec 64)) : CrRep C H 0 ∅ :=
  ⟨[], rfl, fun h => by simp [List.lookup]⟩

theorem crRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {p : BitVec 64}
    {memo : Std.HashMap EIdx Bool} (h : CrRep C H p memo) : CrRep C H' p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_mono hp p xs hm, he⟩

theorem crRep_toH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap EIdx Bool}
    (h : CrRep C H p memo) : CrRep (ctxH C H') H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_toH hm, he⟩

theorem crRep_ofH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {memo : Std.HashMap EIdx Bool}
    (h : CrRep (ctxH C H') H p memo) : CrRep C H p memo :=
  let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_H hm, he⟩

theorem crRep_insert {C : Ctx} {H : List (BitVec 64)} {p' : BitVec 64} {memo : Std.HashMap EIdx Bool}
    {xs : List ((BitVec 64 × BitVec 64) × Bool)}
    (he : ∀ h : EIdx, memo[h]? = xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (h : EIdx) (r : Bool)
    (hm : MNodes C H p' (((Enc.idxW h, BitVec.ofNat 64 0), r) :: xs)) :
    CrRep C H p' (memo.insert h r) := by
  refine ⟨_, hm, fun h' => ?_⟩
  rw [Std.HashMap.getElem?_insert]
  simp only [List.lookup]
  by_cases e : h = h'
  · subst e; simp
  · rw [if_neg (by simpa using e)]
    have : ¬ ((Enc.idxW h', BitVec.ofNat 64 0) == (Enc.idxW h, BitVec.ofNat 64 0)) = true := by
      simp only [beq_iff_eq, Prod.mk.injEq, not_and]
      intro e1 _
      exact e (idxW_inj e1).symm
    simp only [this]
    exact he h'


section
variable {σ : Type}

/-- The answer and memo as a fresh pair block. -/
def PostCr (C : Ctx) (rm : Bool × Std.HashMap EIdx Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o pm, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm ∧
    CrRep C H' pm rm.2 ∧ SR (ctxH C H') s' st

theorem postCr_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCr C a w s' st → PostCr C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, pm, h2, h3, h4, h5, h6, h7⟩ => ⟨H', o, pm, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem specR_crfRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : crfO ∈ D) (her : ∀ w, sev ((crfO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((crfO, w) :: Γ) em = some pm)
    (hrep : CrRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfRet C er em) s (pure (r, memo)) (PostCr (ctxH C H0)) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) crfO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((crfO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv crfO) er H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (boolW r) (by simp <;> rfl) (her _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (boolW r))) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv crfO, .const 8]) em (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) pm (by simp +decide [sev]; exact cellA_add8 C _) (hem _) ?_
  have g0 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length]? = some (boolW r) := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length + 1]? = some pm := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨_, H1.length, pm, h0.trans hpre, rfl, g0, g1, crRep_toH (crRep_mono hpre hrep),
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_crfInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool) (hD : crfN ∈ D ∧ crfO ∈ D) (hH : Γ.get crfH = some (Enc.idxW h))
    (hR : Γ.get crfR = some (boolW r)) (hM : Γ.get crfM2 = some pm)
    (hrep : CrRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfIns C) s (pure (r, memo.insert h r)) (PostCr (ctxH C H0)) := by
  obtain ⟨xs, hm, he⟩ := hrep
  unfold crfIns
  refine specR_mlInsI hok crfN (vv crfH) (.const 0) (vv crfR) (vv crfM2) (Enc.idxW h) (BitVec.ofNat 64 0) pm r xs hD.1
    (fun w => by simp [Env.get, hH]; try (intro e; exact absurd e (by decide))) (fun w => rfl) (fun w => by simp [Env.get, hR]; try (intro e; exact absurd e (by decide)))
    (fun w => by simp [Env.get, hM]; try (intro e; exact absurd e (by decide))) hm (fun H' o hp' hm' => ?_)
  exact specR_crfRetI hok (vv crfR) (vv crfN) r (cellA C o) (memo.insert h r) hD.2
    (fun w => by simp [Env.get, hR]; rw [if_neg (by decide), if_neg (by decide)]) (fun w => by simp [Env.get]; try (intro e; exact absurd e (by decide))) (crRep_insert he h r hm') (h0.trans hp')

theorem crf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crfLocals → (ctxEnv C ++ crfParams.zip vals).get x = none :=
  Knot.params_none C crfLocals crfParams vals (by decide) (by decide)

end

end ConPanqueque.T.Decl
