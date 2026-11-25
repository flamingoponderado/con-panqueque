import ConPanqueque.T.Ind.IotaPartsAt
import ConPanqueque.T.LvlEqList
import ConPanqueque.T.Core.Spine
import ConPanqueque.T.Core.WcStuck
import ConPanqueque.T.Core.FormerSort
import ConPanqueque.T.Core.Beta
import ConPanqueque.T.Core.PeelPis
import ConPanqueque.T.Comp.InferLeaves
import ConPanqueque.T.Comp.TwinFacts

/-!
# Expressions equal up to equivalent levels (`lvlEq`)

`lvlEq fuel a b`: the same handle, or the same constructor with each `Sort` and constant at levels
`Level.isEquiv` decides equal and its parts so related. The twin reads the levels through its readback
caches; the port caches nothing, so the level arms run the twin from the entry state and re-establish the
state relation with `sr_congrS` (the caches only differ in their unmirrored readback tables).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI
open ConPanqueque.T.LLeq ConPanqueque.T.LEq
open ConLeche (Level)

/-- Both level readbacks, then a pure answer: the state differs only in unmirrored caches. -/
theorem readLvl2_run {β : Type} (f : Level → Level → β) (u v : LIdx) (s : AState) (lu lv : Level)
    (hu : denoteL s.store.ls u = some lu) (hv : denoteL s.store.ls v = some lv) (hco : CachesOK s) :
    ∃ s', (readLevelM u >>= fun a => readLevelM v >>= fun b => pure (f a b)) s = .ok (f lu lv, s') ∧
      s'.store = s.store ∧ s'.memos = s.memos ∧ MirrorEq s'.caches s.caches ∧ s'.pins = s.pins ∧ CachesOK s' := by
  obtain ⟨s1, h1, e1, m1, ok1, _, c1, p1⟩ := readLevelM_run u s lu hco.rl hu
  obtain ⟨s2, h2, e2, m2, _, _, c2, p2⟩ := readLevelM_run v s1 lv ok1 (by rw [e1]; exact hv)
  obtain ⟨s1', h1', k1, -⟩ := readLevelM_cok u s lu hco hu
  rw [h1] at h1'; simp only [Except.ok.injEq, Prod.mk.injEq] at h1'; obtain ⟨-, rfl⟩ := h1'
  obtain ⟨s2', h2', k2, -⟩ := readLevelM_cok v s1 lv k1 (by rw [e1]; exact hv)
  rw [h2] at h2'; simp only [Except.ok.injEq, Prod.mk.injEq] at h2'; obtain ⟨-, rfl⟩ := h2'
  refine ⟨s2, ?_, e2.trans e1, m2.trans m1, mirrorEq_trans c2 c1, p2.trans p1, k2⟩
  simp [h1, h2, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]

/-- Both level-list readbacks, then a pure answer. -/
theorem readLvls2_run {β : Type} (f : List Level → List Level → β) (u v : LsIdx) (s : AState) (lu lv : List Level)
    (hu : denoteLs s.store.lss u = some lu) (hv : denoteLs s.store.lss v = some lv) (hco : CachesOK s) :
    ∃ s', (readLevelsM u >>= fun a => readLevelsM v >>= fun b => pure (f a b)) s = .ok (f lu lv, s') ∧
      s'.store = s.store ∧ s'.memos = s.memos ∧ MirrorEq s'.caches s.caches ∧ s'.pins = s.pins ∧ CachesOK s' := by
  obtain ⟨s1, h1, e1, m1, ok1, _, c1, p1⟩ := readLevelsM_run u s lu hco.rls hu
  obtain ⟨s2, h2, e2, m2, _, _, c2, p2⟩ := readLevelsM_run v s1 lv ok1 (by rw [e1]; exact hv)
  obtain ⟨s1', h1', k1, -⟩ := readLevelsM_cok u s lu hco hu
  rw [h1] at h1'; simp only [Except.ok.injEq, Prod.mk.injEq] at h1'; obtain ⟨-, rfl⟩ := h1'
  obtain ⟨s2', h2', k2, -⟩ := readLevelsM_cok v s1 lv k1 (by rw [e1]; exact hv)
  rw [h2] at h2'; simp only [Except.ok.injEq, Prod.mk.injEq] at h2'; obtain ⟨-, rfl⟩ := h2'
  refine ⟨s2, ?_, e2.trans e1, m2.trans m1, mirrorEq_trans c2 c1, p2.trans p1, k2⟩
  simp [h1, h2, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]

def veA := ofString "ve_a"
def veB := ofString "ve_b"
def veTa := ofString "ve_ta"
def vePa := ofString "ve_pa"
def veNa := ofString "ve_na"
def veX1 := ofString "ve_x1"
def veX2 := ofString "ve_x2"
def veX3 := ofString "ve_x3"
def veY1 := ofString "ve_y1"
def veY2 := ofString "ve_y2"
def veY3 := ofString "ve_y3"
def veR := ofString "ve_r"
def fLvlEqE := ofString "lvlEqE"

def veParams : List MlS := [pFu, veA, veB]
def veLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, veTa, vePa, veNa, veX1, veX2, veX3, veY1, veY2, veY3, veR]

def veCall (x a b : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fLvlEqE [.op .sub [vv pFu, .const 1], vv a, vv b]

def veEqC (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .equal (vv x) (.const (BitVec.ofNat 64 k))

def veSort : ProgHOL 64 :=
  .seq (.assign .local veX1 (.load .one (.op .add [vv vePa, .const 0])))
  (.seq (.assign .local veY1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.call (some (some (.local, veR), none)) fEqv [vv veX1, vv veY1]) (.return (veEqC veR 2))))

def veConst : ProgHOL 64 :=
  .seq (.assign .local veX1 (.load .one (.op .add [vv vePa, .const 0])))
  (.seq (.assign .local veY1 (.load .one (.op .add [vv lRp, .const 0])))
  (.ite (.cmp .equal (vv veX1) (vv veY1))
    (.seq (.assign .local veX2 (.load .one (.op .add [vv vePa, .const 8])))
    (.seq (.assign .local veY2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, veR), none)) fLsGo [vv veX2, vv veY2, .const 0]) (.return (veEqC veR 2)))))
    (.return (.const 0))))

/-- Two parts each (`app`, `lam`, `forallE`): both pairs, the second only if the first agrees. -/
def veTwo : ProgHOL 64 :=
  .seq (.assign .local veX1 (.load .one (.op .add [vv vePa, .const 0])))
  (.seq (.assign .local veX2 (.load .one (.op .add [vv vePa, .const 8])))
  (.seq (.assign .local veY1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local veY2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (veCall veR veX1 veY1)
  (.ite (veEqC veR 0) (.return (.const 0))
  (.seq (veCall veR veX2 veY2) (.return (vv veR))))))))

def veLet : ProgHOL 64 :=
  .seq (.assign .local veX1 (.load .one (.op .add [vv vePa, .const 0])))
  (.seq (.assign .local veX2 (.load .one (.op .add [vv vePa, .const 8])))
  (.seq (.assign .local veX3 (.load .one (.op .add [vv vePa, .const 16])))
  (.seq (.assign .local veY1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local veY2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local veY3 (.load .one (.op .add [vv lRp, .const 16])))
  (.seq (veCall veR veX1 veY1)
  (.ite (veEqC veR 0) (.return (.const 0))
  (.seq (veCall veR veX2 veY2)
  (.ite (veEqC veR 0) (.return (.const 0))
  (.seq (veCall veR veX3 veY3) (.return (vv veR))))))))))))

/-- A projection's index word: `0` when the view has two words, the third word when three, else hang. -/
def veIdx (x n p : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (veEqC n 2) (.seq (.assign .local x (.const 0)) rest)
    (.ite (veEqC n 3) (.seq (.assign .local x (.load .one (.op .add [vv p, .const 16]))) rest) hang)

def veProj : ProgHOL 64 :=
  .seq (.assign .local veX1 (.load .one (.op .add [vv vePa, .const 0])))
  (.seq (.assign .local veY1 (.load .one (.op .add [vv lRp, .const 0])))
  (.ite (.cmp .equal (vv veX1) (vv veY1))
    (veIdx veX3 veNa vePa (veIdx veY3 lRn lRp
    (.ite (.cmp .equal (vv veX3) (vv veY3))
      (.seq (.assign .local veX2 (.load .one (.op .add [vv vePa, .const 8])))
      (.seq (.assign .local veY2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (veCall veR veX2 veY2) (.return (vv veR)))))
      (.return (.const 0)))))
    (.return (.const 0))))

def veDispatch : ProgHOL 64 :=
  .ite (veEqC lDg 2) veSort
  (.ite (veEqC lDg 3) veConst
  (.ite (veEqC lDg 4) veTwo
  (.ite (veEqC lDg 5) veTwo
  (.ite (veEqC lDg 6) veTwo
  (.ite (veEqC lDg 7) veLet
  (.ite (veEqC lDg 9) veProj (.return (.const 0))))))))

def veCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.ite (.cmp .equal (vv veA) (vv veB)) (.return (.const 1))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv veA)) (.seq eViewP
  (.seq (.assign .local veTa (vv lDg)) (.seq (.assign .local vePa (vv lRp)) (.seq (.assign .local veNa (vv lRn))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv veB)) (.seq eViewP
  (.ite (.cmp .equal (vv veTa) (vv lDg)) veDispatch (.return (.const 0)))))))))))))

def veBody : ProgHOL 64 := prologue veLocals veCore


section
variable {σ : Type}

/-- The code `lvlEq` runs. -/
structure VECodes (C : Ctx) : Prop where
  ve : C.code.lookup fLvlEqE = some (veParams.map (fun p => (p, ShapeHOL.one)), veBody, .one)
  cS : C.code.lookup LSub.fSubst = some (LSub.substParams.map (fun p => (p, ShapeHOL.one)), LSub.substBody C, .one)
  cN : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  cM : C.code.lookup LSimp.fSimp = some ([(pLa, .one)], LSimp.simpBody C, .one)
  cC : C.code.lookup LComb.fComb = some ([(pLa, .one), (pLb, .one)], LComb.combBody C, .one)
  cB : C.code.lookup fByC = some (LLeq.bcParams.map (fun p => (p, ShapeHOL.one)), LLeq.bcBody C, .one)
  cI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one)
  cR : C.code.lookup fImax = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.imBody C, .one)
  cE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one)
  cT : C.code.lookup fRest = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one)
  cL : C.code.lookup fLeq = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one)
  cV : C.code.lookup fEqv = some ([(pLa, .one), (pLb, .one)], eqvBody, .one)
  cG : C.code.lookup fLsGo = some (lsParams.map (fun p => (p, ShapeHOL.one)), lsGoBody, .one)

def RecVE (C : Ctx) (n : Nat) : Prop :=
  ∀ (H : List (BitVec 64)) (a b : EIdx) (s : AState),
    SpecR (Pre (σ := σ) (ctxH C H) s (veParams.zip [BitVec.ofNat 64 n, Enc.idxW a, Enc.idxW b])) veBody s
      (lvlEq n a b) (PostB (ctxH C H))

theorem ve_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ veLocals → (ctxEnv C ++ veParams.zip vals).get x = none :=
  Knot.params_none C veLocals veParams vals (by decide) (by decide)

theorem obW_eq2 (o : Option Bool) : (obW o == 2#64) = (o == some true) := by
  rcases o with _ | _ | _ <;> rfl

theorem wcE' (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal
    (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a = b) := by
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : a = b
  · subst h; simp
  · simp [h, (ofNat_eq_iff ha hb).not.mpr h]

theorem tag_of_tagN {h : EIdx} {v : ENodeView} (htn : v.tagN = h.tag.toNat) : h.tag = UInt32.ofNat v.tagN := by
  rw [htn]; simp


/-- A recursive call on two words in the environment. -/
theorem veCall_spec {β : Type} (C : Ctx) (hc : VECodes C) (n : Nat) (ih : RecVE (σ := σ) C n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : Bool → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x a b : MlS) (ea eb : EIdx) (hx : x ∈ ctxLocals ++ veLocals)
    (hFu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (ha : Γ.get a = some (Enc.idxW ea))
    (hb : Γ.get b = some (Enc.idxW eb))
    (hk : ∀ r s1 H1, H <+: H1 → SpecR (Inv (ctxH C H1) s1 ((x, boolW r) :: Γ) [] (ctxLocals ++ veLocals)) rest s1 (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) (.seq (veCall x a b) rest) s (lvlEq n ea eb >>= k) R :=
  specR_callNIH (C := ctxH C H) x fLvlEqE veParams [.op .sub [vv pFu, .const 1], vv a, vv b] veBody
    [BitVec.ofNat 64 n, Enc.idxW ea, Enc.idxW eb] (by decide) rfl hx hc.ve
    ⟨by show sev Γ _ = _
        rw [sev_sub2 _ _ _ _ _ (by simp only [sev, sev_vv]; exact hFu) rfl]; congr 1; exact ofNat_succ_sub_one n,
      by simp only [sev, sev_vv]; exact ha, by simp only [sev, sev_vv]; exact hb, trivial⟩
    (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu veParams _ rfl hlk) (ih H ea eb s))
    (fun r w s1 H1 hp1 hw => by subst hw; exact hk r s1 H1 hp1)

/-- The two-part arm (`app`, `lam`, `forallE`). -/
theorem veTwo_spec (C : Ctx) (hc : VECodes C) (n : Nat) (ih : RecVE (σ := σ) C n) (H : List (BitVec 64)) (s : AState)
    (Γ : Env) (M : Mem) (Pa Pb : BitVec 64) (x1 x2 y1 y2 : EIdx)
    (hFu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hPa : Γ.get vePa = some Pa) (hPb : Γ.get lRp = some Pb)
    (m1 : (Pa + BitVec.ofNat 64 0, Enc.idxW x1) ∈ M) (m2 : (Pa + BitVec.ofNat 64 8, Enc.idxW x2) ∈ M)
    (m3 : (Pb + BitVec.ofNat 64 0, Enc.idxW y1) ∈ M) (m4 : (Pb + BitVec.ofNat 64 8, Enc.idxW y2) ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) veTwo s
      (lvlEq n x1 y1 >>= fun r => if r then lvlEq n x2 y2 else pure false) (PostB (ctxH C H)) := by
  unfold veTwo
  refine specR_loadI' veX1 _ _ _ _ (by decide) (by simp [sev, hPa]) rfl m1 ?_
  refine specR_loadI' veX2 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPa]) rfl m2 ?_
  refine specR_loadI' veY1 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPb]) rfl m3 ?_
  refine specR_loadI' veY2 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPb]) rfl m4 ?_
  refine veCall_spec C hc n ih veR veX1 veY1 x1 y1 (by decide) (by simp +decide [Env.get_cons, hFu])
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r s1 H1 hp1 => ?_)
  rcases r
  · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine specR_congr (m' := lvlEq n x2 y2 >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine veCall_spec C hc n ih veR veX2 veY2 x2 y2 (by decide) (by simp +decide [Env.get_cons, hFu])
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r2 s2 H2 hp2 => ?_)
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- The three-part arm (`letE`). -/
theorem veLet_spec (C : Ctx) (hc : VECodes C) (n : Nat) (ih : RecVE (σ := σ) C n) (H : List (BitVec 64)) (s : AState)
    (Γ : Env) (M : Mem) (Pa Pb : BitVec 64) (x1 x2 x3 y1 y2 y3 : EIdx)
    (hFu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hPa : Γ.get vePa = some Pa) (hPb : Γ.get lRp = some Pb)
    (m1 : (Pa + BitVec.ofNat 64 0, Enc.idxW x1) ∈ M) (m2 : (Pa + BitVec.ofNat 64 8, Enc.idxW x2) ∈ M)
    (m3 : (Pa + BitVec.ofNat 64 16, Enc.idxW x3) ∈ M)
    (m4 : (Pb + BitVec.ofNat 64 0, Enc.idxW y1) ∈ M) (m5 : (Pb + BitVec.ofNat 64 8, Enc.idxW y2) ∈ M)
    (m6 : (Pb + BitVec.ofNat 64 16, Enc.idxW y3) ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) veLet s
      (lvlEq n x1 y1 >>= fun r => if r then (lvlEq n x2 y2 >>= fun r2 => if r2 then lvlEq n x3 y3 else pure false)
        else pure false) (PostB (ctxH C H)) := by
  unfold veLet
  refine specR_loadI' veX1 _ _ _ _ (by decide) (by simp [sev, hPa]) rfl m1 ?_
  refine specR_loadI' veX2 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPa]) rfl m2 ?_
  refine specR_loadI' veX3 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPa]) rfl m3 ?_
  refine specR_loadI' veY1 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPb]) rfl m4 ?_
  refine specR_loadI' veY2 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPb]) rfl m5 ?_
  refine specR_loadI' veY3 _ _ _ _ (by decide) (by simp +decide [sev, Env.get_cons, hPb]) rfl m6 ?_
  refine veCall_spec C hc n ih veR veX1 veY1 x1 y1 (by decide) (by simp +decide [Env.get_cons, hFu])
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r s1 H1 hp1 => ?_)
  rcases r
  · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine veCall_spec C hc n ih veR veX2 veY2 x2 y2 (by decide) (by simp +decide [Env.get_cons, hFu])
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r2 s2 H2 hp2 => ?_)
  rcases r2
  · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine specR_congr (m' := lvlEq n x3 y3 >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine veCall_spec C hc n ih veR veX3 veY3 x3 y3 (by decide) (by simp +decide [Env.get_cons, hFu])
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r3 s3 H3 hp3 => ?_)
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H3, (hp1.trans hp2).trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- A projection view's index word. -/
theorem veIdx_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (x nv p : MlS) (P : BitVec 64) (c : NIdx) (i : Nat)
    (e : EIdx) (hx : x ∈ D) (hn : Γ.get nv = some (BitVec.ofNat 64 (encEView (.proj c i e)).length))
    (hp : Γ.get p = some P) (hM : ∀ q, q ∈ wordsAt P (encEView (.proj c i e)) → q ∈ M)
    (hlen : (encEView (.proj c i e)).length < 2 ^ 61)
    (hk : i < 2 ^ 64 → SpecR (Inv C s ((x, BitVec.ofNat 64 i) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (veIdx x nv p rest) s m R := by
  unfold veIdx
  have hlenP : (encEView (.proj c i e)).length = 2 + (Enc.limbs i).length := by
    simp [encEView, Enc.encProj]; omega
  by_cases i0 : i = 0
  · subst i0
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, hn, hlenP, Enc.limbs,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    exact specR_assignI x (.const 0) (BitVec.ofNat 64 0) hx rfl (hk (by decide))
  · by_cases ib : i < 2 ^ 64
    · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenP, hl,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [veEqC, sev, hn, hlenP, hl,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_loadI' x _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) hx
        (by simp +decide [sev, hp]) rfl
        (hM _ (by simpa [encEView, Enc.encProj, hl] using
          wordsAt_get P [Enc.idxW c, Enc.idxW e, BitVec.ofNat 64 i] 2 (by simp) [])) ?_
      exact hk ib
    · have hl := limbs_len_ge2 i (by omega)
      have hlt' : (Enc.limbs i).length < 2 ^ 61 := by omega
      have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenP, hn2,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenP, hn3,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)

/-- The projection arm. -/
theorem veProj_spec (C : Ctx) (hc : VECodes C) (n : Nat) (ih : RecVE (σ := σ) C n) (H : List (BitVec 64)) (s : AState)
    (Γ : Env) (M : Mem) (Pa Pb : BitVec 64) (c c' : NIdx) (i i' : Nat) (x y : EIdx)
    (hFu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hPa : Γ.get vePa = some Pa) (hPb : Γ.get lRp = some Pb)
    (hNa : Γ.get veNa = some (BitVec.ofNat 64 (encEView (.proj c i x)).length))
    (hNb : Γ.get lRn = some (BitVec.ofNat 64 (encEView (.proj c' i' y)).length))
    (hMa : ∀ q, q ∈ wordsAt Pa (encEView (.proj c i x)) → q ∈ M)
    (hMb : ∀ q, q ∈ wordsAt Pb (encEView (.proj c' i' y)) → q ∈ M)
    (hla : (encEView (.proj c i x)).length < 2 ^ 61) (hlb : (encEView (.proj c' i' y)).length < 2 ^ 61) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) veProj s
      (if c == c' then (if i == i' then lvlEq n x y else pure false) else pure false) (PostB (ctxH C H)) := by
  unfold veProj
  refine specR_loadI' veX1 _ (Pa + 0) (Pa + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev, hPa]) rfl
    (hMa _ (by simpa [encEView, Enc.encProj] using wordsAt_mem0 Pa (Enc.idxW c) (Enc.idxW x :: Enc.limbs i) [])) ?_
  refine specR_loadI' veY1 _ (Pb + 0) (Pb + BitVec.ofNat 64 0) (Enc.idxW c') (by decide)
    (by simp +decide [sev, Env.get_cons, hPb]) rfl
    (hMb _ (by simpa [encEView, Enc.encProj] using wordsAt_mem0 Pb (Enc.idxW c') (Enc.idxW y :: Enc.limbs i') [])) ?_
  have ret0 : ∀ (Γ' : Env), SpecR (σ := σ) (Inv (ctxH C H) s Γ' M (ctxLocals ++ veLocals)) (.return (.const 0)) s
      (pure false) (PostB (ctxH C H)) := fun Γ' =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases hcc : c = c'
  · subst hcc
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ite_true]
    refine veIdx_spec veX3 veNa vePa Pa c i x (by decide) (by simp +decide [Env.get_cons, hNa])
      (by simp +decide [Env.get_cons, hPa]) hMa hla (fun hi => ?_)
    refine veIdx_spec veY3 lRn lRp Pb c i' y (by decide) (by simp +decide [Env.get_cons, hNb])
      (by simp +decide [Env.get_cons, hPb]) hMb hlb (fun hi' => ?_)
    by_cases hii : i = i'
    · subst hii
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ite_true]
      refine specR_loadI' veX2 _ (Pa + 8) (Pa + BitVec.ofNat 64 8) (Enc.idxW x) (by decide)
        (by simp +decide [sev, Env.get_cons, hPa]) rfl
        (hMa _ (by simpa [encEView, Enc.encProj] using wordsAt_mem1 Pa (Enc.idxW c) (Enc.idxW x) (Enc.limbs i) [])) ?_
      refine specR_loadI' veY2 _ (Pb + 8) (Pb + BitVec.ofNat 64 8) (Enc.idxW y) (by decide)
        (by simp +decide [sev, Env.get_cons, hPb]) rfl
        (hMb _ (by simpa [encEView, Enc.encProj] using wordsAt_mem1 Pb (Enc.idxW c) (Enc.idxW y) (Enc.limbs i) [])) ?_
      refine specR_congr (m' := lvlEq n x y >>= fun r => pure r) (by rw [bind_pure]) ?_
      refine veCall_spec C hc n ih veR veX2 veY2 x y (by decide) (by simp +decide [Env.get_cons, hFu])
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun r s1 H1 hp1 => ?_)
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 i' := (ofNat_eq_iff hi hi').not.mpr hii
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      have : (i == i') = false := by simpa using hii
      simp only [this, Bool.false_eq_true, ite_false]
      exact ret0 _
  · have hne : Enc.idxW c ≠ Enc.idxW c' := fun e => hcc (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    have : (c == c') = false := by simpa using hcc
    simp only [this, Bool.false_eq_true, ite_false]
    exact ret0 _


/-- The sort arm, against the pure answer. -/
theorem veSort_spec (C : Ctx) (hok : CtxOK C) (hc : VECodes C) (H : List (BitVec 64)) (s : AState)
    (Γ : Env) (M : Mem) (Pa Pb : BitVec 64) (u u' : LIdx) (lu lu' : Level)
    (hu : denoteL s.store.ls u = some lu) (hu' : denoteL s.store.ls u' = some lu')
    (hPa : Γ.get vePa = some Pa) (hPb : Γ.get lRp = some Pb)
    (m1 : (Pa + BitVec.ofNat 64 0, Enc.idxW u) ∈ M) (m2 : (Pb + BitVec.ofNat 64 0, Enc.idxW u') ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) veSort s
      (pure (Level.isEquiv lu lu' == some true)) (PostB (ctxH C H)) := by
  unfold veSort
  refine specR_loadI' veX1 _ (Pa + 0) (Pa + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp [sev, hPa]) rfl m1 ?_
  refine specR_loadI' veY1 _ (Pb + 0) (Pb + BitVec.ofNat 64 0) (Enc.idxW u') (by decide)
    (by simp +decide [sev, Env.get_cons, hPb]) rfl m2 ?_
  refine specR_congr (m' := pure (Level.isEquiv lu lu') >>= fun o => pure (o == some true)) (by simp) ?_
  refine specR_callNIH (C := ctxH C H) veR fEqv [pLa, pLb] [vv veX1, vv veY1] eqvBody [Enc.idxW u, Enc.idxW u']
    (by decide) rfl (by decide) hc.cV ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostOB (ctxH C H)) (fun o w _ _ => w = obW o) (fun o w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, hw, hsr⟩)
    (fun v hv _ hlk => Knot.specR_of_pre v (pre_of_lookups hv [pLa, pLb] _ rfl hlk)
      (eqv_spec C hok hc.cS hc.cN hc.cM hc.cC hc.cB hc.cI hc.cR hc.cE hc.cT hc.cL H lu lu' _ _ s
        (lrep_arena _ _ _ u _ lu hu) (lrep_arena _ _ _ u' _ lu' hu')))
    (fun o w s1 H1 hp1 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW (o == some true)) (by
      simp only [veEqC]
      rw [sev_cmp2 _ _ _ _ (obW o) (BitVec.ofNat 64 2) (by simp [sev, Env.get_cons]) rfl]
      rcases o with _ | _ | _ <;> rfl)
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The const arm at equal names, against the pure answer. -/
theorem veConst_spec (C : Ctx) (hok : CtxOK C) (hc : VECodes C) (H : List (BitVec 64)) (s : AState)
    (Γ : Env) (M : Mem) (Pa Pb : BitVec 64) (us us' : LsIdx) (ua ub : List LIdx) (lu lu' : List Level)
    (ha : s.store.lss.view us = some ua) (hb : s.store.lss.view us' = some ub)
    (hua : denoteLList s.store.ls ua = some lu) (hub : denoteLList s.store.ls ub = some lu')
    (hPa : Γ.get vePa = some Pa) (hPb : Γ.get lRp = some Pb)
    (m2 : (Pa + BitVec.ofNat 64 8, Enc.idxW us) ∈ M) (m4 : (Pb + BitVec.ofNat 64 8, Enc.idxW us') ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals))
      (.seq (.assign .local veX2 (.load .one (.op .add [vv vePa, .const 8])))
      (.seq (.assign .local veY2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, veR), none)) fLsGo [vv veX2, vv veY2, .const 0]) (.return (veEqC veR 2))))) s
      (pure (Level.isEquivList lu lu' == some true)) (PostB (ctxH C H)) := by
  refine specR_loadI' veX2 _ (Pa + 8) (Pa + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp [sev, hPa]) rfl m2 ?_
  refine specR_loadI' veY2 _ (Pb + 8) (Pb + BitVec.ofNat 64 8) (Enc.idxW us') (by decide)
    (by simp +decide [sev, Env.get_cons, hPb]) rfl m4 ?_
  refine specR_congr (m' := pure (Level.isEquivList (lu.drop 0) (lu'.drop 0)) >>= fun o => pure (o == some true))
    (by simp) ?_
  refine specR_callNIH (C := ctxH C H) veR fLsGo lsParams [vv veX2, vv veY2, .const 0] lsGoBody
    [Enc.idxW us, Enc.idxW us', BitVec.ofNat 64 0]
    (by decide) rfl (by decide) hc.cG ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
      trivial⟩
    (PostOB (ctxH C H)) (fun o w _ _ => w = obW o) (fun o w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, hw, hsr⟩)
    (fun v hv _ hlk => Knot.specR_of_pre v (pre_of_lookups hv lsParams _ rfl hlk)
      (lsGo_spec C hok hc.cS hc.cN hc.cM hc.cC hc.cB hc.cI hc.cR hc.cE hc.cT hc.cL hc.cV hc.cG H us us' ua ub lu lu' s
        ha hb hua hub _ 0 rfl (Nat.zero_le _) (Nat.zero_le _)))
    (fun o w s1 H1 hp1 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW (o == some true)) (by
      simp only [veEqC]
      rw [sev_cmp2 _ _ _ _ (obW o) (BitVec.ofNat 64 2) (by simp [sev, Env.get_cons]) rfl]
      rcases o with _ | _ | _ <;> rfl)
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`lvlEq`** at fuel below `2 ^ 63`. -/
theorem ve_spec (C : Ctx) (hok : CtxOK C) (hc : VECodes C) : ∀ n, n < 2 ^ 63 → RecVE (σ := σ) C n := by
  intro n
  induction n with
  | zero =>
    intro _ H a b s
    refine specR_prologue (postB_locals _) (ve_none _ _) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sev, Env.get, veParams, ctxEnv] at hw
  | succ n ih =>
    intro hf H a b s
    have ih' := ih (by omega)
    refine specR_prologue (postB_locals _) (ve_none _ _) ?_
    let Γ0 : Env := ctxEnv (ctxH C H) ++ veParams.zip [BitVec.ofNat 64 (n + 1), Enc.idxW a, Enc.idxW b]
    have gFu : Γ0.get pFu = some (BitVec.ofNat 64 (n + 1)) := by simp +decide [Γ0, Env.get, veParams, ctxEnv]
    have gA : Γ0.get veA = some (Enc.idxW a) := by simp +decide [Γ0, Env.get, veParams, ctxEnv]
    have gB : Γ0.get veB = some (Enc.idxW b) := by simp +decide [Γ0, Env.get, veParams, ctxEnv]
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ _ _ (by simp only [sev, sev_vv]; exact gFu) rfl]
        have := ofNat_ne_zero (n + 1) (by omega) (by omega)
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this)
      (fun hw => absurd rfl hw) (fun _ => ?_)
    rw [lvlEq]
    by_cases hab : a = b
    · subst hab
      refine specR_ifI _ 1 (by
          rw [sev_cmp2 _ _ _ _ _ _ (by simp only [sev, sev_vv]; exact gA) (by simp only [sev, sev_vv]; exact gA)]
          simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ite_true]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hne : Enc.idxW a ≠ Enc.idxW b := fun e => hab (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ _ _ (by simp only [sev, sev_vv]; exact gA) (by simp only [sev, sev_vv]; exact gB)]
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun hw => absurd rfl hw) (fun _ => ?_)
    have hab' : (a == b) = false := by simpa using hab
    simp only [hab', Bool.false_eq_true, ite_false]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, veParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv veA) (Enc.idxW a) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gA) ?_
    refine ConPanqueque.T.Big.specR_viewP a (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, veParams, ctxEnv] <;> rfl) (by decide) (fun va Pa hva htna hlena => ?_)
    refine specR_assignI veTa (vv lDg) (BitVec.ofNat 64 va.tagN) (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_assignI vePa (vv lRp) Pa (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    refine specR_assignI veNa (vv lRn) (BitVec.ofNat 64 (encEView va).length) (by decide)
      (by simp +decide [sev, Env.get_cons]) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, veParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv veB) (Enc.idxW b) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gB) ?_
    refine ConPanqueque.T.Big.specR_viewP b (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, veParams, ctxEnv] <;> rfl) (by decide) (fun vb Pb hvb htnb hlenb => ?_)
    have hta : va.tagN < 16 := ConPanqueque.T.Big.tagN_lt va
    have htb : vb.tagN < 16 := ConPanqueque.T.Big.tagN_lt vb
    have tagEq : (a.tag == b.tag) = (va.tagN == vb.tagN) := by
      rw [tag_of_tagN htna, tag_of_tagN htnb]
      by_cases e : va.tagN = vb.tagN
      · simp [e]
      · have : UInt32.ofNat va.tagN ≠ UInt32.ofNat vb.tagN := by
          intro h; have := congrArg UInt32.toNat h; simp at this; omega
        simp [e, this]
    refine specR_ifI _ (boolW (va.tagN == vb.tagN)) (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 va.tagN) (BitVec.ofNat 64 vb.tagN) (by simp +decide [sev, Env.get_cons])
          (by simp +decide [sev, Env.get_cons])]
        by_cases e : va.tagN = vb.tagN
        · simp [e, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        · simp [e, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ofNat_eq_iff (a := va.tagN) (b := vb.tagN)
            (by omega) (by omega)]) (fun hw => ?_) (fun hw => ?_)
    swap
    · have e : (va.tagN == vb.tagN) = false := by
        cases h : (va.tagN == vb.tagN) <;> simp_all [boolW]
      rw [tagEq, e]; simp only [Bool.false_eq_true, ite_false]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have e : (va.tagN == vb.tagN) = true := by
      cases h : (va.tagN == vb.tagN) <;> simp_all [boolW]
    rw [tagEq, e]; simp only [ite_true]
    have hEq : va.tagN = vb.tagN := by simpa using e
    have hat : a.tag = UInt32.ofNat va.tagN := tag_of_tagN htna
    have gDg : ∀ k, k < 16 → sev ((lRp, Pb) :: (lRn, BitVec.ofNat 64 (encEView vb).length) ::
        (lDt, BitVec.ofNat 64 b.tier.toNat) :: (lDg, BitVec.ofNat 64 vb.tagN) :: (lDi, BitVec.ofNat 64 b.idxNat) ::
        (lDh, Enc.idxW b) :: (lFl, C.FLe) :: (veNa, BitVec.ofNat 64 (encEView va).length) :: (vePa, Pa) ::
        (veTa, BitVec.ofNat 64 va.tagN) :: (lRp, Pa) :: (lRn, BitVec.ofNat 64 (encEView va).length) ::
        (lDt, BitVec.ofNat 64 a.tier.toNat) :: (lDg, BitVec.ofNat 64 va.tagN) :: (lDi, BitVec.ofNat 64 a.idxNat) ::
        (lDh, Enc.idxW a) :: (lFl, C.FLe) :: Γ0) (veEqC lDg k) = some (boolW (va.tagN == k)) := fun k hk => by
      rw [hEq]; unfold veEqC
      rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vb.tagN) (BitVec.ofNat 64 k) (by simp [sev, Env.get_cons]) rfl,
        wcE' _ _ (by omega) (by omega)]
      by_cases h : vb.tagN = k <;> simp [h, boolW]
    have no : ∀ k, (va.tagN == k) = false → boolW (va.tagN == k) = 0 := fun k e => by simp [e, boolW]
    have yes : ∀ k, (va.tagN == k) = true → boolW (va.tagN == k) ≠ 0 := fun k e => by simp [e, boolW]
    unfold veDispatch
    have ret0 : ∀ (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ veLocals)) (.return (.const 0)) s
        (pure false) (PostB (ctxH C H)) := fun Γ M =>
      specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    cases va with
    | bvar i =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 9 (by decide)) (fun hw => absurd (no 9 rfl) hw) (fun _ => ?_)
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      exact ret0 _ _
    | fvar idx ty =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 9 (by decide)) (fun hw => absurd (no 9 rfl) hw) (fun _ => ?_)
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      exact ret0 _ _
    | lit l =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 9 (by decide)) (fun hw => absurd (no 9 rfl) hw) (fun _ => ?_)
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      exact ret0 _ _
    | sort u =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 2 rfl))
      rcases vb with _ | _ | u' | _ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      have hta : a.tag = ETag.sort := by rw [hat]; rfl
      have htb : b.tag = ETag.sort := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewSort a s = .ok (some u, s) by
        rw [Comp.viewSort_run, WC.viewSort_of_view hta hva]) ?_
      refine specR_runBind (show viewSort b s = .ok (some u', s) by
        rw [Comp.viewSort_run, WC.viewSort_of_view htb hvb]) ?_
      refine specR_fact (fun t ht => And.intro ht.sr.cok (And.intro (sr_sortDen ht.sr a u hva) (sr_sortDen ht.sr b u' hvb)))
        (fun ⟨hco, ⟨lu, hlu⟩, ⟨lu', hlu'⟩⟩ => ?_)
      obtain ⟨s', hrun, e1, e2, e3, e4, hco'⟩ :=
        readLvl2_run (fun x y => Level.isEquiv x y == some true) u u' s lu lu' hlu hlu' hco
      exact specR_ofRun hrun (veSort_spec C hok hc H s _ _ Pa Pb u u' lu lu' hlu hlu'
          (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
          (List.mem_append_right _ (by simpa [encEView, Enc.encSort] using wordsAt_mem0 Pa (Enc.idxW u) [] []))
          (by simpa [encEView, Enc.encSort] using wordsAt_mem0 Pb (Enc.idxW u') [] _))
        (fun w st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_congrS hsr e1 e2 e3 e4 hco'⟩)
    | const nm us =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 3 rfl))
      rcases vb with _ | _ | _ | ⟨nm', us'⟩ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      have hta : a.tag = ETag.const := by rw [hat]; rfl
      have htb : b.tag = ETag.const := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewConst a s = .ok (some (nm, us), s) by
        rw [WC.viewConst_run, WC.viewConst_of_view hta hva]) ?_
      refine specR_runBind (show viewConst b s = .ok (some (nm', us'), s) by
        rw [WC.viewConst_run, WC.viewConst_of_view htb hvb]) ?_
      unfold veConst
      refine specR_loadI' veX1 _ (Pa + 0) (Pa + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (List.mem_append_right _ (by simpa [encEView, Enc.encConst] using wordsAt_mem0 Pa (Enc.idxW nm) [Enc.idxW us] [])) ?_
      refine specR_loadI' veY1 _ (Pb + 0) (Pb + BitVec.ofNat 64 0) (Enc.idxW nm') (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem0 Pb (Enc.idxW nm') [Enc.idxW us'] _) ?_
      by_cases hn : nm = nm'
      · subst hn
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [beq_self_eq_true, ite_true]
        refine specR_fact (fun t ht => And.intro ht.sr.cok (And.intro
          (Comp.sr_lsChild ht.sr hva (us := us) (by simp [ENodeView.lschildren]))
          (Comp.sr_lsChild ht.sr hvb (us := us') (by simp [ENodeView.lschildren]))))
          (fun ⟨hco, ⟨lu, hlu⟩, ⟨lu', hlu'⟩⟩ => ?_)
        obtain ⟨s', hrun, e1, e2, e3, e4, hco'⟩ :=
          readLvls2_run (fun x y => Level.isEquivList x y == some true) us us' s lu lu' hlu hlu' hco
        have hu1 := hlu; have hu2 := hlu'
        unfold denoteLs at hu1 hu2
        split at hu1
        · simp at hu1
        rename_i ua hua
        split at hu2
        · simp at hu2
        rename_i ub hub
        exact specR_ofRun hrun (veConst_spec C hok hc H s _ _ Pa Pb us us' ua ub lu lu' hua hub hu1 hu2
            (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
            (List.mem_append_right _ (by simpa [encEView, Enc.encConst] using wordsAt_mem1 Pa (Enc.idxW nm) (Enc.idxW us) [] []))
            (by simpa [encEView, Enc.encConst] using wordsAt_mem1 Pb (Enc.idxW nm) (Enc.idxW us') [] _))
          (fun w st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_congrS hsr e1 e2 e3 e4 hco'⟩)
      · have hne : Enc.idxW nm ≠ Enc.idxW nm' := fun e => hn (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
          (fun h => absurd rfl h) (fun _ => ?_)
        have : (nm == nm') = false := by simpa using hn
        simp only [this, Bool.false_eq_true, ite_false]
        exact ret0 _ _
    | app f x =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 4 rfl))
      rcases vb with _ | _ | _ | _ | ⟨g, y⟩ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      have hta : a.tag = ETag.app := by rw [hat]; rfl
      have htb : b.tag = ETag.app := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewApp a s = .ok (some (f, x), s) by
        rw [viewApp_run, WC.viewApp_of_view hta hva]) ?_
      refine specR_runBind (show viewApp b s = .ok (some (g, y), s) by
        rw [viewApp_run, WC.viewApp_of_view htb hvb]) ?_
      exact veTwo_spec C hc n ih' H s _ _ Pa Pb f x g y (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
        (List.mem_append_right _ (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pa (Enc.idxW f) [Enc.idxW x] []))
        (List.mem_append_right _ (by simpa [encEView, Enc.encApp] using wordsAt_mem1 Pa (Enc.idxW f) (Enc.idxW x) [] []))
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pb (Enc.idxW g) [Enc.idxW y] _)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 Pb (Enc.idxW g) (Enc.idxW y) [] _)
    | lam ty x =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 5 rfl))
      rcases vb with _ | _ | _ | _ | _ | ⟨ty', y⟩ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true, Bool.or_true,
        Bool.true_or]
      have hta : a.tag = ETag.lam := by rw [hat]; rfl
      have htb : b.tag = ETag.lam := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewBind a s = .ok (some (ty, x), s) by
        rw [WC.viewBind_run, WC.viewBind_of_view_lam hta hva]) ?_
      refine specR_runBind (show viewBind b s = .ok (some (ty', y), s) by
        rw [WC.viewBind_run, WC.viewBind_of_view_lam htb hvb]) ?_
      exact veTwo_spec C hc n ih' H s _ _ Pa Pb ty x ty' y (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
        (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty) [Enc.idxW x] []))
        (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty) (Enc.idxW x) [] []))
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty') [Enc.idxW y] _)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty') (Enc.idxW y) [] _)
    | forallE ty x =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 6 rfl))
      rcases vb with _ | _ | _ | _ | _ | _ | ⟨ty', y⟩ | _ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true, Bool.or_true,
        Bool.true_or]
      have hta : a.tag = ETag.forallE := by rw [hat]; rfl
      have htb : b.tag = ETag.forallE := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewBind a s = .ok (some (ty, x), s) by
        rw [WC.viewBind_run, WC.viewBind_of_view_forallE hta hva]) ?_
      refine specR_runBind (show viewBind b s = .ok (some (ty', y), s) by
        rw [WC.viewBind_run, WC.viewBind_of_view_forallE htb hvb]) ?_
      exact veTwo_spec C hc n ih' H s _ _ Pa Pb ty x ty' y (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
        (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty) [Enc.idxW x] []))
        (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty) (Enc.idxW x) [] []))
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty') [Enc.idxW y] _)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty') (Enc.idxW y) [] _)
    | letE ty v x =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 7 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 7 rfl))
      rcases vb with _ | _ | _ | _ | _ | _ | _ | ⟨ty', v', y⟩ | _ | _ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      have hta : a.tag = 7 := by rw [hat]; rfl
      have htb : b.tag = 7 := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewLet a s = .ok (some (ty, v, x), s) by
        show (pure (s.store.viewLet a) : AM _) s = _
        rw [viewLet_bind _ _ hta, hva]; rfl) ?_
      refine specR_runBind (show viewLet b s = .ok (some (ty', v', y), s) by
        show (pure (s.store.viewLet b) : AM _) s = _
        rw [viewLet_bind _ _ htb, hvb]; rfl) ?_
      exact veLet_spec C hc n ih' H s _ _ Pa Pb ty v x ty' v' y (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
        (List.mem_append_right _ (by simpa [encEView, Enc.encLet] using wordsAt_mem0 Pa (Enc.idxW ty) [Enc.idxW v, Enc.idxW x] []))
        (List.mem_append_right _ (by simpa [encEView, Enc.encLet] using wordsAt_mem1 Pa (Enc.idxW ty) (Enc.idxW v) [Enc.idxW x] []))
        (List.mem_append_right _ (by simpa [encEView, Enc.encLet] using wordsAt_mem2 Pa (Enc.idxW ty) (Enc.idxW v) (Enc.idxW x) [] []))
        (by simpa [encEView, Enc.encLet] using wordsAt_mem0 Pb (Enc.idxW ty') [Enc.idxW v', Enc.idxW y] _)
        (by simpa [encEView, Enc.encLet] using wordsAt_mem1 Pb (Enc.idxW ty') (Enc.idxW v') [Enc.idxW y] _)
        (by simpa [encEView, Enc.encLet] using wordsAt_mem2 Pb (Enc.idxW ty') (Enc.idxW v') (Enc.idxW y) [] _)
    | proj sn i x =>
      refine specR_ifI _ _ (gDg 2 (by decide)) (fun hw => absurd (no 2 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 3 (by decide)) (fun hw => absurd (no 3 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (gDg 9 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 9 rfl))
      rcases vb with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨sn', i', y⟩ <;> simp [ENodeView.tagN] at hEq
      simp +decide only [hat, ENodeView.tagN, ite_true, ite_false, Bool.or_self, Bool.false_eq_true]
      have hta : a.tag = 9 := by rw [hat]; rfl
      have htb : b.tag = 9 := by rw [tag_of_tagN htnb]; rfl
      refine specR_runBind (show viewProj a s = .ok (some (sn, i, x), s) by
        show (pure (s.store.viewProj a) : AM _) s = _
        rw [viewProj_bind _ _ hta, hva]; rfl) ?_
      refine specR_runBind (show viewProj b s = .ok (some (sn', i', y), s) by
        show (pure (s.store.viewProj b) : AM _) s = _
        rw [viewProj_bind _ _ htb, hvb]; rfl) ?_
      exact veProj_spec C hc n ih' H s _ _ Pa Pb sn sn' i i' x y (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons])
        (fun q hq => List.mem_append_right _ (List.mem_append_left _ hq)) (fun q hq => List.mem_append_left _ hq)
        hlena hlenb

end

end ConPanqueque.T.Ind
