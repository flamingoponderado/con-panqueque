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
  (.ite (.op .or [.op .or [.cmp .equal (vv lDg) (.const 0), .cmp .equal (vv lDg) (.const 2)],
      .op .or [.cmp .equal (vv lDg) (.const 3), .cmp .equal (vv lDg) (.const 8)]])
    (.seq (.call (some (some (.local, crfR), none)) fCrl [vv crfH]) (crfRet C (vv crfR) (vv crfM)))
  (.seq (.call (some (some (.local, crfL), none)) fMl [vv crfM, vv crfH, .const 0])
  (.ite (.cmp .notEqual (vv crfL) (.const 0)) (crfRet C (.op .sub [vv crfL, .const 1]) (vv crfM))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv crfH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local crfC1 (.load .one (vv lRp))) (crfCall crfK1 (vv crfC1) (vv crfM) (crfIns C)))
  (.ite (.op .or [.op .or [.cmp .equal (vv lDg) (.const 4), .cmp .equal (vv lDg) (.const 5)], .cmp .equal (vv lDg) (.const 6)])
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8]))) (crfArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local crfC3 (.load .one (.op .add [vv lRp, .const 16]))) (crfArm3 C))))
    (crfProj C)))))))))))))

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
  · rw [ite_eq_right (by simpa using e)]
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
    (fun w => by simp [Env.get, hR]; rw [ite_eq_right (by decide), ite_eq_right (by decide)]) (fun w => by simp [Env.get]; try (intro e; exact absurd e (by decide))) (crRep_insert he h r hm') (h0.trans hp')

theorem crf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crfLocals → (ctxEnv C ++ crfParams.zip vals).get x = none :=
  Knot.params_none C crfLocals crfParams vals (by decide) (by decide)


structure CrfCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  self : C.code.lookup fCrf = some (crfParams.map (fun p => (p, ShapeHOL.one)), crfBody C, .one)
  leaf : C.code.lookup fCrl = some ([crH].map (fun p => (p, ShapeHOL.one)), crLeafBody C, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)

/-- The walk's spec at fuel `n`, for every argument. -/
def CrfRec (C : Ctx) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → CrRep C H pm memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (crfParams.zip [BitVec.ofNat 64 n, Enc.idxW h, pm]))
      (crfBody C) s (constsResolveFGo C.fe memo n h) (PostCr (ctxH C H))

/-- One recursive call, then the pair block read back. -/
theorem specR_crfCallI {α : Type} {C : Ctx} (hc : CrfCodes C) {n : Nat} (ih : CrfRec (σ := σ) C n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap EIdx Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eH eM : ExpHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hx : x ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D) (hxn : x ≠ crfR ∧ crfM2 ≠ x) (hp : C.H <+: H) (hrep : CrRep C H pm memo)
    (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1)))
    (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap EIdx Bool) H' pm' w s', H <+: H' → CrRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s' ((crfM2, pm') :: (crfR, boolW rm.1) :: (x, w) :: Γ) [] D) rest s' (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (crfCall x eH eM rest) s (constsResolveFGo C.fe memo n h >>= k) R := by
  unfold crfCall
  refine specR_callNIH (C := ctxH C H) x fCrf crfParams [.op .sub [vv crfF, .const 1], eH, eM] (crfBody C)
    [BitVec.ofNat 64 n, Enc.idxW h, pm] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, heH, heM, trivial⟩
    (PostCr (ctxH C H))
    (fun rm w s' H' => ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      CrRep C H' pm' rm.2)
    (fun rm w s' st ⟨H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨o, pm', hw, h0, h1', crRep_ofH hrep'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crfParams _ rfl hlk) (ih h memo H s pm hp hrep))
    (fun rm w s' H' hp' ⟨o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H') crfR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') crfM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) s' hp' hrep'


theorem boolW_and (a b : Bool) : boolW a &&& boolW b = boolW (a && b) := by cases a <;> cases b <;> decide

theorem specR_crfArm2I {C : Ctx} (hok : CtxOK C) (hc : CrfCodes C) {n : Nat} (ih : CrfRec (σ := σ) C n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx)
    (c1 c2 : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : crfK1 ∈ D ∧ crfK2 ∈ D ∧ crfR ∈ D ∧ crfR2 ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1)))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm)
    (hC1 : Γ.get crfC1 = some (Enc.idxW c1)) (hC2 : Γ.get crfC2 = some (Enc.idxW c2)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfArm2 C) s
      (do
        let d1 ← constsResolveFGo C.fe memo n c1
        let d2 ← constsResolveFGo C.fe d1.2 n c2
        let y ← pure (d1.1 && d2.1, d2.2)
        pure (y.1, y.2.insert h y.1)) (PostCr (ctxH C H0)) := by
  unfold crfArm2
  refine specR_crfCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  dsimp only
  refine specR_assignI crfR2 (vv crfR) (boolW b1) hD.2.2.2.1 (by simp +decide [Env.get]) ?_
  refine specR_crfCallI hc ih crfK2 (vv crfC2) (vv crfM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp +decide [Env.get, hF]) (by simp +decide [Env.get, hC2])
    (by simp +decide [Env.get]) (fun rm H2 pm2 w2 s2 hp2 hrep2 => ?_)
  obtain ⟨b2, m2⟩ := rm
  dsimp only
  refine specR_assignI crfR (.op .and [vv crfR2, vv crfR]) (boolW (b1 && b2)) hD.2.2.1
    (by simp +decide [sev, Env.get, boolW_and]) ?_
  simp only [pure_bind]
  exact specR_crfInsI hok h (b1 && b2) pm2 m2 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
    (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep2 (h0.trans (hp1.trans hp2))


theorem specR_crfArm3I {C : Ctx} (hok : CtxOK C) (hc : CrfCodes C) {n : Nat} (ih : CrfRec (σ := σ) C n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx)
    (c1 c2 c3 : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : crfK1 ∈ D ∧ crfK2 ∈ D ∧ crfK3 ∈ D ∧ crfR ∈ D ∧ crfR2 ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D)
    (hp : C.H <+: H) (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1)))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm)
    (hC1 : Γ.get crfC1 = some (Enc.idxW c1)) (hC2 : Γ.get crfC2 = some (Enc.idxW c2))
    (hC3 : Γ.get crfC3 = some (Enc.idxW c3)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfArm3 C) s
      (do
        let d1 ← constsResolveFGo C.fe memo n c1
        let d2 ← constsResolveFGo C.fe d1.2 n c2
        let d3 ← constsResolveFGo C.fe d2.2 n c3
        let y ← pure (d1.1 && d2.1 && d3.1, d3.2)
        pure (y.1, y.2.insert h y.1)) (PostCr (ctxH C H0)) := by
  unfold crfArm3
  refine specR_crfCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.2.2.1, hD.2.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  dsimp only
  refine specR_assignI crfR2 (vv crfR) (boolW b1) hD.2.2.2.2.1 (by simp +decide [Env.get]) ?_
  refine specR_crfCallI hc ih crfK2 (vv crfC2) (vv crfM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.2.1, hD.2.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp +decide [Env.get, hF]) (by simp +decide [Env.get, hC2])
    (by simp +decide [Env.get]) (fun rm H2 pm2 w2 s2 hp2 hrep2 => ?_)
  obtain ⟨b2, m2⟩ := rm
  dsimp only
  refine specR_assignI crfR2 (.op .and [vv crfR2, vv crfR]) (boolW (b1 && b2)) hD.2.2.2.2.1
    (by simp +decide [sev, Env.get, boolW_and]) ?_
  refine specR_crfCallI hc ih crfK3 (vv crfC3) (vv crfM2) c3 pm2 m2 ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ ((hp.trans hp1).trans hp2) hrep2 (by simp +decide [Env.get, hF])
    (by simp +decide [Env.get, hC3]) (by simp +decide [Env.get]) (fun rm H3 pm3 w3 s3 hp3 hrep3 => ?_)
  obtain ⟨b3, m3⟩ := rm
  dsimp only
  refine specR_assignI crfR (.op .and [vv crfR2, vv crfR]) (boolW (b1 && b2 && b3)) hD.2.2.2.1
    (by simp +decide [sev, Env.get, boolW_and, Bool.and_assoc]) ?_
  simp only [pure_bind]
  exact specR_crfInsI hok h (b1 && b2 && b3) pm3 m3 ⟨hD.2.2.2.2.2.2.1, hD.2.2.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
    (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep3 (h0.trans (hp1.trans (hp2.trans hp3)))

theorem specR_crfArm1I {C : Ctx} (hok : CtxOK C) (hc : CrfCodes C) {n : Nat} (ih : CrfRec (σ := σ) C n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 : EIdx) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool) (hD : crfK1 ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1)))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm) (hC1 : Γ.get crfC1 = some (Enc.idxW c1)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfCall crfK1 (vv crfC1) (vv crfM) (crfIns C)) s
      (constsResolveFGo C.fe memo n c1 >>= fun p => pure (p.1, p.2.insert h p.1)) (PostCr (ctxH C H0)) := by
  refine specR_crfCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.1, hD.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  exact specR_crfInsI hok h rm.1 pm1 rm.2 ⟨hD.2.2.2.1, hD.2.2.2.2⟩ (by simp +decide [Env.get, hH])
    (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)


theorem specR_crfProjK {C : Ctx} (hok : CtxOK C) (hc : CrfCodes C) {n : Nat} (ih : CrfRec (σ := σ) C n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h sub : EIdx) (sn : NIdx)
    (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : crfK1 ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D ∧ crfY ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1)))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm) (hC1 : Γ.get crfC1 = some (Enc.idxW sub))
    (hS : Γ.get crfS = some (Enc.idxW sn)) (hkb : Γ.get lKb = some C.KB) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D)
      (crfCall crfK1 (vv crfC1) (vv crfM) (envFindP C crfY (vv crfS)
        (.ite (.cmp .equal (vv crfY) (.const 0)) (.seq (.assign .local crfR (.const 0)) (crfIns C)) (crfIns C)))) s
      (do
        let d ← constsResolveFGo C.fe memo n sub
        let y ← pure ((C.fe.find? sn).isSome && d.1, d.2)
        pure (y.1, y.2.insert h y.1)) (PostCr (ctxH C H0)) := by
  refine specR_crfCallI hc ih crfK1 (vv crfC1) (vv crfM) sub pm memo ⟨hD.1, hD.2.1, hD.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 s1 hp1 hrep1 => ?_)
  obtain ⟨b, m1⟩ := rm
  dsimp only
  simp only [pure_bind]
  have hok1 := ctxOK_H hok H1
  refine specR_envFindI hok1 hc.mg hc.mp crfY (vv crfS) sn hD.2.2.2.2.2 (by simp +decide [sev, Env.get, hS])
    (by simp +decide [Env.get, hkb]; rfl) ?_
  have hrel := find_rel hok1 sn
  revert hrel
  rcases hf : (ctxH C H1).fe.find? sn with _ | ci
  · intro hrel
    simp only at hrel
    rw [hrel]
    have hf' : C.fe.find? sn = none := hf
    refine specR_ifI _ 1 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_assignI crfR (.const 0) (boolW false) hD.2.1 rfl ?_
    simp only [hf', Option.isSome_none, Bool.false_and]
    exact specR_crfInsI hok h false pm1 m1 ⟨hD.2.2.2.1, hD.2.2.2.2.1⟩ (by simp +decide [Env.get, hH])
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)
  · intro ⟨o, hm, hci⟩
    rw [hm]
    have hf' : C.fe.find? sn = some ci := hf
    refine specR_atEntry fun t ht => ?_
    have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, vv, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [hf', Option.isSome_some, Bool.true_and]
    exact specR_crfInsI hok h b pm1 m1 ⟨hD.2.2.2.1, hD.2.2.2.2.1⟩ (by simp +decide [Env.get, hH])
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)


theorem crf_spec (C : Ctx) (hok : CtxOK C) (hc : CrfCodes C) : ∀ n, n < 2 ^ 64 → CrfRec (σ := σ) C n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo H s pm hp hrep
    refine specR_prologue (postCr_locals _) (crf_none _ _) ?_
    unfold crfCore
    rw [constsResolveFGo]
    exact specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn h memo H s pm hp hrep
  have ih' := ih (by omega)
  obtain ⟨xs, hm, he⟩ := id hrep
  have hok' := ctxOK_H hok H
  refine specR_prologue (postCr_locals _) (crf_none _ _) ?_
  unfold crfCore
  rw [constsResolveFGo]
  have hne := ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq h v _ s hv) ?_
  -- the leaf arm
  have hleafK : ∀ {Γ : Env} {M : Mem}, (∀ v', s.store.view h = some v' → v'.tagN = 0 ∨ v'.tagN = 2 ∨ v'.tagN = 3 ∨ v'.tagN = 8) →
      Γ.get crfH = some (Enc.idxW h) → Γ.get crfM = some pm →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ crfLocals))
        (.seq (.call (some (some (.local, crfR), none)) fCrl [vv crfH]) (crfRet C (vv crfR) (vv crfM))) s
        (constsResolve C.fe coreWalkFuel h >>= fun b => pure (b, memo)) (PostCr (ctxH C H)) := by
    intro Γ M hleaf hH hM
    refine specR_callNIH (C := ctxH C H) crfR fCrl [crH] [vv crfH] (crLeafBody C) [Enc.idxW h] (by decide) rfl
      (by decide) hc.leaf ⟨by simp [sev, hH], trivial⟩ (PostB (ctxH C H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crH] _ rfl hlk)
        (cr_leaf_spec (ctxH C H) hok' hc.mg hc.mp s h hleaf))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_crfRetI hok (vv crfR) (vv crfM) b pm memo (by decide) (fun w => by simp +decide [Env.get])
      (fun w => by simp +decide [Env.get, hM]) (crRep_mono hp1 hrep) hp1
  rcases v with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, vl, b⟩ | l | ⟨pn, pi, sub⟩
  · -- bvar
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hleafK (fun v' hv' => by rw [hv] at hv'; cases hv'; simp [ENodeView.tagN]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
  · -- fvar
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
      exact specR_crfArm1I (D := ctxLocals ++ crfLocals) hok hc ih' h ty pm memo ⟨by decide, by decide, by decide, by decide, by decide⟩ hp
        (List.prefix_refl _) hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
  · -- sort
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hleafK (fun v' hv' => by rw [hv] at hv'; cases hv'; simp [ENodeView.tagN]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
  · -- const
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hleafK (fun v' hv' => by rw [hv] at hv'; cases hv'; simp [ENodeView.tagN]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
  · -- app
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW a] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW f) (Enc.idxW a) [] []) ?_
      refine specR_crfArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h f a pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) <;> try rfl
  · -- lam
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_crfArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h ty b pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) <;> try rfl
  · -- forallE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_crfArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h ty b pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) <;> try rfl
  · -- letE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW vl, Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW vl) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW vl) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW vl) (Enc.idxW b) [] []) ?_
      refine specR_crfArm3I (D := ctxLocals ++ crfLocals) hok hc ih' h ty vl b pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
        hp (List.prefix_refl _) hrep ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) <;> try rfl
  · -- lit
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hleafK (fun v' hv' => by rw [hv] at hv'; cases hv'; simp [ENodeView.tagN]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv])
  · -- proj
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
      [pm, Enc.idxW h, BitVec.ofNat 64 0] (xs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
      ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv], rfl, trivial⟩
      (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
      (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
        (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) xs pm H s (mnodes_toH hm)))
      (fun w H' _ ⟨hw, hH'⟩ => ?_)
    subst hw; subst H'
    rw [he h]
    cases hlk : xs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
    | some r =>
      have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_crfRetI hok _ (vv crfM) r pm memo (by decide)
        (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
        (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) hrep (List.prefix_refl _)
    | none =>
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v' P hv' _ _ => ?_)
      rw [hv] at hv'
      cases hv'
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      unfold crfProj
      refine specR_loadI' crfS (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW pn) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW pn) (Enc.idxW sub :: Enc.limbs pi) []) ?_
      refine specR_loadI' crfC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW pn) (Enc.idxW sub) (Enc.limbs pi) []) ?_
      refine specR_crfProjK (D := ctxLocals ++ crfLocals) hok hc ih' h sub pn pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
        hp (List.prefix_refl _) hrep ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, crfParams, ctxEnv]) <;> try rfl

def crffE := ofString "crff_e"
def crffK := ofString "crff_k"
def crffR := ofString "crff_r"

/-- `constsResolveFFast`: the walk from an empty memo, its answer read off the pair block. -/
def crffBody : ProgHOL 64 := prologue [crffK, crffR]
  (.seq (.call (some (some (.local, crffK), none)) fCrf [.const (BitVec.ofNat 64 coreWalkFuel), vv crffE, .const 0])
  (.seq (.assign .local crffR (.load .one (vv crffK))) (.return (vv crffR))))

theorem crff_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ [crffK, crffR] → (ctxEnv C ++ [crffE].zip vals).get x = none :=
  Knot.params_none C [crffK, crffR] [crffE] vals (by decide) (by decide)

/-- **`constsResolveFFast`**. -/
theorem crff_spec (C : Ctx) (hok : CtxOK C) (hc : CrfCodes C) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s ([crffE].zip [Enc.idxW e])) crffBody s (constsResolveFFast C.fe e) (PostB C) := by
  refine specR_prologue (postB_locals C) (crff_none C _) ?_
  unfold constsResolveFFast
  refine specR_callNIH (C := C) crffK fCrf crfParams [.const (BitVec.ofNat 64 coreWalkFuel), vv crffE, .const 0]
    (crfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0] (by decide) rfl (by decide) hc.self
    ⟨rfl, by simp +decide [Env.get, ctxEnv], rfl, trivial⟩ (PostCr C)
    (fun rm w _ H' => ∃ o, w = cellA C o ∧ H'[o]? = some (boolW rm.1))
    (fun rm w s' st ⟨H', o, pm, hp', hw, h0, _, _, hsr⟩ => ⟨H', hp', ⟨o, hw, h0⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crfParams _ rfl hlk)
      (crf_spec C hok hc coreWalkFuel CV.coreWalkFuel_lt e ∅ C.H s 0 (List.prefix_refl _) (crRep_empty C C.H)))
    (fun rm w s1 H1 hp1 ⟨o, hw, h0⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) crffR (vv crffK) o (boolW rm.1) h0 (by decide) (by simp [Env.get]; rfl) ?_
  exact specR_returnI _ (boolW rm.1) (by simp +decide [Env.get])
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
