import ConPanqueque.T.Ex.Inst1Fast
import ConPanqueque.T.Ex.Lift
import ConPanqueque.T.Ex.BvarBound
import ConPanqueque.T.Heap
import ConPanqueque.T.InstLP
import ConPanqueque.T.Ex.InstList
import ConPanqueque.Front.Tbl
import ConPanqueque.T.Core.Unfold
import ConPanqueque.T.Core.AndRescue

/-!
# `instantiateLiftGo`: substitute several variables, lifting the values

The twin's `instantiateLiftGo vs fuel h d` (replace `bvar (d + j)` by the `j`-th value from the end, lifted past
the `d` binders crossed; lower the variables above the values): the `bvarB` cutoff, one view, the dispatch on
its tag, and arms that read their parts off the view, probe the `inst1L` memo, rebuild through the interns
and record the answer.  `instLiftGo(vs, n, fu, h, d)`: the values in cells from `vs + 1`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.ExIL
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI

def fInstL := ofString "instLiftGo"
def pVs := ofString "ilvs"
def pVn := ofString "ilvn"

def ilParams : List MlS := [pVs, pVn, pFu, pH, pD]

def callIL (x arg : MlS) (dE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fInstL [vv pVs, vv pVn, .op .sub [vv pFu, .const 1], vv arg, dE]

/-- The `bvar` arm once `bb` holds the index `i`. -/
def bvarRestIL : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
  (.ite (.cmp .lower (vv lB) (vv pD)) (.return (vv pH))
  (.ite (.cmp .lower (.op .sub [vv lB, vv pD]) (vv pVn))
    (.seq (.assign .local lA1 (.load .one (.op .add [vv pVs, .shift .lsl (.op .sub [vv pVn, .op .sub [vv lB, vv pD]])
        (.const 3)])))
    (.seq (.call (some (some (.local, lW), none)) ExL.fLiftF [.op .sub [vv pFu, .const 1], vv pD, .const 0, vv lA1])
      (.return (vv lW))))
    (.seq (.call (some (some (.local, lW), none)) fInternBVar [.op .sub [vv lB, vv pVn]]) (.return (vv lW)))))

def bvarArmIL : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local lB (.const 0)) bvarRestIL)
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 0])))
      bvarRestIL) hang)

def appArmIL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (probed G (.seq (callIL lY lA1 (vv pD)) (.seq (callIL lZ lA2 (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ])
    (memoSetP G (.return (vv lW))))))))

def bindArmIL (G : BitVec 64) (fn : MlS) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
  (.ite (.shift .lsr (vv lD1) (.const 63)) hang
  (probed G (.seq (callIL lY lA1 (vv pD)) (.seq (callIL lZ lA2 (vv lD1))
    (.seq (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ])
    (memoSetP G (.return (vv lW))))))))))

def letArmIL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
  (.seq (.assign .local lD1 (.op .add [vv pD, .const 1]))
  (.ite (.shift .lsr (vv lD1) (.const 63)) hang
  (probed G (.seq (callIL lY lA1 (vv pD)) (.seq (callIL lZ lA2 (vv pD)) (.seq (callIL lB lA3 (vv lD1))
    (.seq (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB])
    (memoSetP G (.return (vv lW))))))))))))

def projRestIL (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
  (probed G (.seq (callIL lY lA2 (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (memoSetP G (.return (vv lW))))))

def projArmIL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestIL G))
    (.ite (.cmp .equal (vv lRn) (.const 3))
      (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestIL G)) hang)))

def eqTag (k : Nat) : ExpHOL 64 := .cmp .equal (vv lDg) (.const (BitVec.ofNat 64 k))

def coreIL (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.call (some (some (.local, lB), none)) ExB.fBvarB [.op .sub [vv pFu, .const 1], vv pH])
  (.ite (.cmp .lower (vv pD) (vv lB))
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.ite (eqTag 0) bvarArmIL
    (.ite (eqTag 4) (appArmIL G)
    (.ite (eqTag 5) (bindArmIL G fInternLam)
    (.ite (eqTag 6) (bindArmIL G fInternForallE)
    (.ite (eqTag 7) (letArmIL G)
    (.ite (eqTag 9) (projArmIL G) (.return (vv pH)))))))))))
    (.return (vv pH))))

def bodyIL (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreIL (C.mG (.e .inst1L)))

/-- The code map holds the walk and every function it calls. -/
structure CodesIL (C : Ctx) : Prop where
  il : C.code.lookup fInstL = some (ilParams.map (fun p => (p, ShapeHOL.one)), bodyIL C, .one)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  cb : ExB.CodesB C (ExB.bodyB C)
  liftF : C.code.lookup ExL.fLiftF = some ([(pFu, .one), (ExL.pA, .one), (pD, .one), (pH, .one)], ExL.fastBodyL C, .one)
  cl : ExL.CodesL C (ExL.bodyL C)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  internApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  internLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  internForallE : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  internLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  internBVar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  internProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)

theorem instantiateLiftGo_succ (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    instantiateLiftGo vs (fuel + 1) h d = (do
      let bb ← bvarB fuel h
      if bb ≤ d then pure h
      else
        match ← view h with
        | .bvar i =>
          if i < d then pure h
          else if hlt : i - d < vs.size then
            liftLooseBVarsFast fuel d 0 (vs[vs.size - 1 - (i - d)]'(by omega))
          else internE (.bvar (i - vs.size))
        | .fvar _ _ => pure h
        | .sort _ => pure h
        | .const _ _ => pure h
        | .lit _ => pure h
        | .app f a => instLiftArmApp vs fuel h d f a
        | .lam ty bd => instLiftArmLam vs fuel h d ty bd
        | .forallE ty bd => instLiftArmForallE vs fuel h d ty bd
        | .letE ty val bd => instLiftArmLet vs fuel h d ty val bd
        | .proj n i sub => instLiftArmProj vs fuel h d n i sub) := by
  rw [instantiateLiftGo]; congr 1

theorem inst1LGet_run (k : EIdx × Nat) (s : AState) : inst1LGet k s = .ok ((memoSel .inst1L s.memos)[k]?, s) := rfl
theorem inst1LSet_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    inst1LSet k r s = .ok ((), { s with memos := memoUpd .inst1L s.memos ((memoSel .inst1L s.memos).insert k r) }) := rfl

section
variable {σ : Type}

/-- The values `vs` in cells from `ov + 1`. -/
def VsAt (C : Ctx) (ov : Nat) (vs : Array EIdx) : Prop :=
  vs.size < 2 ^ 59 ∧ ∀ j (hj : j < vs.size), C.H[ov + 1 + j]? = some (Enc.idxW vs[j])

/-- The walk's spec at fuel `n`. -/
def RecIL (C : Ctx) (ov : Nat) (vs : Array EIdx) (n : Nat) : Prop :=
  ∀ (h : EIdx) (d : Nat) (s : AState), d < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s (ilParams.zip [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 n, Enc.idxW h,
      BitVec.ofNat 64 d])) (bodyIL C) s (instantiateLiftGo vs n h d) (PostE C)

theorem callIL_spec {β : Type} (C : Ctx) (hc : CodesIL C) (ov : Nat) (vs : Array EIdx) (n : Nat)
    (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (dE : ExpHOL 64) (c : EIdx) (d : Nat)
    (hd : d < 2 ^ 63) (hx : x ∈ DI)
    (hvs : Γ.get pVs = some (cellA C ov)) (hvn : Γ.get pVn = some (BitVec.ofNat 64 vs.size))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (harg : Γ.get arg = some (Enc.idxW c)) (hdE : sev Γ dE = some (BitVec.ofNat 64 d))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callIL x arg dE) rest) s (instantiateLiftGo vs n c d >>= k) R :=
  ILP.callE_spec x fInstL ilParams [vv pVs, vv pVn, .op .sub [vv pFu, .const 1], vv arg, dE] (bodyIL C)
    [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 n, Enc.idxW c, BitVec.ofNat 64 d] (by decide) rfl hx hc.il
    ⟨by simp [sev, hvs], by simp [sev, hvn], by simp [sev, hfu]; exact ofNat_succ_sub_one n, by simp [sev, harg], hdE,
      trivial⟩ (ih c d s hd) hk

/-- The memo probe: a hit answers; a miss runs `miss`. -/
theorem probedIL_spec {C : Ctx} (hok : CtxOK C) (hc : CodesIL C) {s : AState} {Γ : Env} {M : Mem} {miss : ProgHOL 64}
    {m : AM EIdx} (h : EIdx) (d : Nat) (hd : d < 2 ^ 63)
    (hh : Γ.get pH = some (Enc.idxW h)) (hdd : Γ.get pD = some (BitVec.ofNat 64 d)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (σ := σ) (Inv C s ((lX, 0) :: Γ) [] DI) miss s m (PostE C)) :
    SpecR (σ := σ) (Inv C s Γ M DI) (probed (C.mG (.e .inst1L)) miss) s
      (do match ← inst1LGet (h, d) with
          | some r => pure r
          | none => m) (PostE C) := by
  unfold probed memoGetP
  refine specR_memoGetI hok .inst1L inst1LGet inst1LGet_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h d hd
    (by decide) (by simp [hh]) (by simp [hdd]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW, optWG]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    refine specR_ifI (vv lX) 0 (by simp [optW, optWG]) (fun hw => absurd rfl hw) (fun _ => ?_)
    exact hmiss

end

section
variable {σ : Type}

/-- The facts every arm reads: the parameters, the key buffer, and the view's words at `P`. -/
structure ArmEnv (C : Ctx) (ov : Nat) (vs : Array EIdx) (n : Nat) (h : EIdx) (d : Nat) (Γ : Env) : Prop where
  gvs : Γ.get pVs = some (cellA C ov)
  gvn : Γ.get pVn = some (BitVec.ofNat 64 vs.size)
  gfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))
  ghh : Γ.get pH = some (Enc.idxW h)
  gdd : Γ.get pD = some (BitVec.ofNat 64 d)
  gkb : Γ.get lKb = some C.KB

theorem armEnv_cons {C : Ctx} {ov : Nat} {vs : Array EIdx} {n : Nat} {h : EIdx} {d : Nat} {Γ : Env}
    (ha : ArmEnv C ov vs n h d Γ) (x : MlS) (v : BitVec 64) (hx : x ≠ pVs ∧ x ≠ pVn ∧ x ≠ pFu ∧ x ≠ pH ∧ x ≠ pD ∧ x ≠ lKb) :
    ArmEnv C ov vs n h d ((x, v) :: Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  exact ⟨by rw [Env.get_cons, ite_eq_right (Ne.symm h1)]; exact ha.gvs, by rw [Env.get_cons, ite_eq_right (Ne.symm h2)]; exact ha.gvn,
    by rw [Env.get_cons, ite_eq_right (Ne.symm h3)]; exact ha.gfu, by rw [Env.get_cons, ite_eq_right (Ne.symm h4)]; exact ha.ghh,
    by rw [Env.get_cons, ite_eq_right (Ne.symm h5)]; exact ha.gdd, by rw [Env.get_cons, ite_eq_right (Ne.symm h6)]; exact ha.gkb⟩

theorem appArmIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (n : Nat) (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (f a : EIdx) (P : BitVec 64) (ha : ArmEnv C ov vs n h d Γ)
    (hp : Γ.get lRp = some P) (hm0 : (P, Enc.idxW f) ∈ M) (hm1 : (P + 8, Enc.idxW a) ∈ M) :
    SpecR (σ := σ) (Inv C s Γ M DI) (appArmIL (C.mG (.e .inst1L))) s (instLiftArmApp vs n h d f a) (PostE C) := by
  refine specR_congr (by rw [instLiftArmApp]) ?_
  unfold appArmIL
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev, hp]) (by simp) hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev, hp]) rfl
    hm1 ?_
  have ha2 := armEnv_cons (armEnv_cons ha lA1 (Enc.idxW f) (by decide)) lA2 (Enc.idxW a) (by decide)
  refine probedIL_spec hok hc h d hd ha2.ghh ha2.gdd ha2.gkb ?_
  have ha3 := armEnv_cons ha2 lX 0 (by decide)
  refine callIL_spec C hc ov vs n ih lY lA1 (vv pD) f d hd (by decide) ha3.gvs ha3.gvn ha3.gfu (by simp +decide [Env.get_cons])
    (by simp only [sev, sev_vv]; exact ha3.gdd) (fun f' s1 => ?_)
  have ha4 := armEnv_cons ha3 lY (Enc.idxW f') (by decide)
  refine callIL_spec C hc ov vs n ih lZ lA2 (vv pD) a d hd (by decide) ha4.gvs ha4.gvn ha4.gfu (by simp +decide [Env.get_cons])
    (by simp only [sev, sev_vv]; exact ha4.gdd) (fun a' s2 => ?_)
  have ha5 := armEnv_cons ha4 lZ (Enc.idxW a') (by decide)
  refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [sev, Env.get_cons]) (fun r s3 => ?_)
  have ha6 := armEnv_cons ha5 lW (Enc.idxW r) (by decide)
  unfold memoSetP
  refine specR_memoSetI hok .inst1L inst1LSet inst1LSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp only [sev, sev_vv]; exact ha6.ghh) (by simp only [sev, sev_vv]; exact ha6.gdd) (by simp +decide [sev, Env.get_cons]) ha6.gkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem lamArmIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (n : Nat) (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (ty bd : EIdx) (P : BitVec 64) (ha : ArmEnv C ov vs n h d Γ)
    (hp : Γ.get lRp = some P) (hm0 : (P, Enc.idxW ty) ∈ M) (hm1 : (P + 8, Enc.idxW bd) ∈ M) :
    SpecR (σ := σ) (Inv C s Γ M DI) (bindArmIL (C.mG (.e .inst1L)) fInternLam) s (instLiftArmLam vs n h d ty bd) (PostE C) := by
  refine specR_congr (by rw [instLiftArmLam]) ?_
  unfold bindArmIL
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW ty) (by decide) (by simp [sev, hp]) (by simp) hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW bd) (by decide) (by simp +decide [sev, hp]) rfl hm1 ?_
  have ha2 := armEnv_cons (armEnv_cons ha lA1 (Enc.idxW ty) (by decide)) lA2 (Enc.idxW bd) (by decide)
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp only [sev, sev_vv, ha2.gdd]; simp; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev, Env.get_cons]) (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
  have ha2' := armEnv_cons ha2 lD1 (BitVec.ofNat 64 (d + 1)) (by decide)
  refine probedIL_spec hok hc h d hd ha2'.ghh ha2'.gdd ha2'.gkb ?_
  have ha3 := armEnv_cons ha2' lX 0 (by decide)
  refine callIL_spec C hc ov vs n ih lY lA1 (vv pD) ty d hd (by decide) ha3.gvs ha3.gvn ha3.gfu
    (by simp +decide [Env.get_cons]) (by simp only [sev, sev_vv]; exact ha3.gdd) (fun t' s1 => ?_)
  have ha4 := armEnv_cons ha3 lY (Enc.idxW t') (by decide)
  refine callIL_spec C hc ov vs n ih lZ lA2 (vv lD1) bd (d + 1) hlt (by decide) ha4.gvs ha4.gvn ha4.gfu
    (by simp +decide [Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun b' s2 => ?_)
  have ha5 := armEnv_cons ha4 lZ (Enc.idxW b') (by decide)
  refine specR_internLamI ra hok hc.internLam lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [sev, Env.get_cons]) (fun r s3 => ?_)
  have ha6 := armEnv_cons ha5 lW (Enc.idxW r) (by decide)
  unfold memoSetP
  refine specR_memoSetI hok .inst1L inst1LSet inst1LSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp only [sev, sev_vv]; exact ha6.ghh) (by simp only [sev, sev_vv]; exact ha6.gdd)
    (by simp +decide [sev, Env.get_cons]) ha6.gkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem forallEArmIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (n : Nat) (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (ty bd : EIdx) (P : BitVec 64) (ha : ArmEnv C ov vs n h d Γ)
    (hp : Γ.get lRp = some P) (hm0 : (P, Enc.idxW ty) ∈ M) (hm1 : (P + 8, Enc.idxW bd) ∈ M) :
    SpecR (σ := σ) (Inv C s Γ M DI) (bindArmIL (C.mG (.e .inst1L)) fInternForallE) s (instLiftArmForallE vs n h d ty bd) (PostE C) := by
  refine specR_congr (by rw [instLiftArmForallE]) ?_
  unfold bindArmIL
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW ty) (by decide) (by simp [sev, hp]) (by simp) hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW bd) (by decide) (by simp +decide [sev, hp]) rfl hm1 ?_
  have ha2 := armEnv_cons (armEnv_cons ha lA1 (Enc.idxW ty) (by decide)) lA2 (Enc.idxW bd) (by decide)
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp only [sev, sev_vv, ha2.gdd]; simp; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev, Env.get_cons]) (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
  have ha2' := armEnv_cons ha2 lD1 (BitVec.ofNat 64 (d + 1)) (by decide)
  refine probedIL_spec hok hc h d hd ha2'.ghh ha2'.gdd ha2'.gkb ?_
  have ha3 := armEnv_cons ha2' lX 0 (by decide)
  refine callIL_spec C hc ov vs n ih lY lA1 (vv pD) ty d hd (by decide) ha3.gvs ha3.gvn ha3.gfu
    (by simp +decide [Env.get_cons]) (by simp only [sev, sev_vv]; exact ha3.gdd) (fun t' s1 => ?_)
  have ha4 := armEnv_cons ha3 lY (Enc.idxW t') (by decide)
  refine callIL_spec C hc ov vs n ih lZ lA2 (vv lD1) bd (d + 1) hlt (by decide) ha4.gvs ha4.gvn ha4.gfu
    (by simp +decide [Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun b' s2 => ?_)
  have ha5 := armEnv_cons ha4 lZ (Enc.idxW b') (by decide)
  refine specR_internForallEI ra hok hc.internForallE lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [sev, Env.get_cons]) (fun r s3 => ?_)
  have ha6 := armEnv_cons ha5 lW (Enc.idxW r) (by decide)
  unfold memoSetP
  refine specR_memoSetI hok .inst1L inst1LSet inst1LSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp only [sev, sev_vv]; exact ha6.ghh) (by simp only [sev, sev_vv]; exact ha6.gdd)
    (by simp +decide [sev, Env.get_cons]) ha6.gkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem letArmIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (n : Nat) (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (ty val bd : EIdx) (P : BitVec 64) (ha : ArmEnv C ov vs n h d Γ)
    (hp : Γ.get lRp = some P) (hm0 : (P, Enc.idxW ty) ∈ M) (hm1 : (P + 8, Enc.idxW val) ∈ M)
    (hm2 : (P + 16, Enc.idxW bd) ∈ M) :
    SpecR (σ := σ) (Inv C s Γ M DI) (letArmIL (C.mG (.e .inst1L))) s (instLiftArmLet vs n h d ty val bd) (PostE C) := by
  refine specR_congr (by rw [instLiftArmLet]) ?_
  unfold letArmIL
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW ty) (by decide) (by simp [sev, hp]) (by simp) hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW val) (by decide) (by simp +decide [sev, hp]) rfl hm1 ?_
  refine specR_loadI' lA3 _ (P + 16) (P + 16) (Enc.idxW bd) (by decide) (by simp +decide [sev, hp]) rfl hm2 ?_
  have ha2 := armEnv_cons (armEnv_cons (armEnv_cons ha lA1 (Enc.idxW ty) (by decide)) lA2 (Enc.idxW val) (by decide))
    lA3 (Enc.idxW bd) (by decide)
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp only [sev, sev_vv, ha2.gdd]; simp; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (d + 1) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev, Env.get_cons]) (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero (d + 1) (by omega)).mp hw
  have ha2' := armEnv_cons ha2 lD1 (BitVec.ofNat 64 (d + 1)) (by decide)
  refine probedIL_spec hok hc h d hd ha2'.ghh ha2'.gdd ha2'.gkb ?_
  have ha3 := armEnv_cons ha2' lX 0 (by decide)
  refine callIL_spec C hc ov vs n ih lY lA1 (vv pD) ty d hd (by decide) ha3.gvs ha3.gvn ha3.gfu
    (by simp +decide [Env.get_cons]) (by simp only [sev, sev_vv]; exact ha3.gdd) (fun t' s1 => ?_)
  have ha4 := armEnv_cons ha3 lY (Enc.idxW t') (by decide)
  refine callIL_spec C hc ov vs n ih lZ lA2 (vv pD) val d hd (by decide) ha4.gvs ha4.gvn ha4.gfu
    (by simp +decide [Env.get_cons]) (by simp only [sev, sev_vv]; exact ha4.gdd) (fun w' s2 => ?_)
  have ha5 := armEnv_cons ha4 lZ (Enc.idxW w') (by decide)
  refine callIL_spec C hc ov vs n ih lB lA3 (vv lD1) bd (d + 1) hlt (by decide) ha5.gvs ha5.gvn ha5.gfu
    (by simp +decide [Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (fun b' s3 => ?_)
  have ha6 := armEnv_cons ha5 lB (Enc.idxW b') (by decide)
  refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' w' b' (by decide)
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons])
    (fun r s4 => ?_)
  have ha7 := armEnv_cons ha6 lW (Enc.idxW r) (by decide)
  unfold memoSetP
  refine specR_memoSetI hok .inst1L inst1LSet inst1LSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp only [sev, sev_vv]; exact ha7.ghh) (by simp only [sev, sev_vv]; exact ha7.gdd)
    (by simp +decide [sev, Env.get_cons]) ha7.gkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The `proj` arm once `bb` holds the field index. -/
theorem projRestIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (n : Nat) (ih : RecIL (σ := σ) C ov vs n) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (c : NIdx) (i : Nat) (sub : EIdx) (hi : i < 2 ^ 64)
    (ha : ArmEnv C ov vs n h d Γ) (ha1 : Γ.get lA1 = some (Enc.idxW c)) (ha2 : Γ.get lA2 = some (Enc.idxW sub))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (σ := σ) (Inv C s Γ M DI) (projRestIL (C.mG (.e .inst1L))) s (instLiftArmProj vs n h d c i sub) (PostE C) := by
  refine specR_congr (by rw [instLiftArmProj]) ?_
  unfold projRestIL
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine probedIL_spec hok hc h d hd ha.ghh ha.gdd ha.gkb ?_
  have ha3 := armEnv_cons ha lX 0 (by decide)
  refine callIL_spec C hc ov vs n ih lY lA2 (vv pD) sub d hd (by decide) ha3.gvs ha3.gvn ha3.gfu
    (by simp +decide [Env.get_cons, ha2]) (by simp only [sev, sev_vv]; exact ha3.gdd) (fun u s1 => ?_)
  have ha4 := armEnv_cons ha3 lY (Enc.idxW u) (by decide)
  refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) c i u hi63 (by decide)
    (by simp +decide [sev, Env.get_cons, ha1]) (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, hb])
    (fun r s2 => ?_)
  have ha5 := armEnv_cons ha4 lW (Enc.idxW r) (by decide)
  unfold memoSetP
  refine specR_memoSetI hok .inst1L inst1LSet inst1LSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h d r hd
    (by decide) (by simp only [sev, sev_vv]; exact ha5.ghh) (by simp only [sev, sev_vv]; exact ha5.gdd)
    (by simp +decide [sev, Env.get_cons]) ha5.gkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

/-- The `bvar` arm once `bb` holds the index. -/
theorem bvarRestIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (hvs : VsAt C ov vs) (n : Nat) (hn : n < 2 ^ 63) {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (i : Nat) (hi : i < 2 ^ 64) (ha : ArmEnv C ov vs n h d Γ)
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (σ := σ) (Inv C s Γ M DI) bvarRestIL s
      (if i < d then pure h
       else if hlt : i - d < vs.size then liftLooseBVarsFast n d 0 (vs[vs.size - 1 - (i - d)]'(by omega))
       else internE (.bvar (i - vs.size))) (PostE C) := by
  obtain ⟨hsz, hcells⟩ := hvs
  unfold bvarRestIL
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ (vv lB) (vv pD) i d (by simp [sev, hb])
    (by simp only [sev, sev_vv]; exact ha.gdd) (by omega) (by omega)) (fun h1 => ?_) (fun h1 => ?_)
  · have c : i < d := by by_cases c : i < d; exact c; simp [bw, c] at h1
    rw [if_pos c]
    exact specR_returnI _ _ (by simp only [sev, sev_vv]; exact ha.ghh) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have c : ¬ i < d := by intro c; simp [bw, c] at h1
  rw [if_neg c]
  have hsub : sev Γ (.op .sub [vv lB, vv pD]) = some (BitVec.ofNat 64 (i - d)) := by
    simp only [sev, sev_vv, hb, ha.gdd]; simp; exact ExP.word_sub_eq i d (by omega) (by omega)
  refine specR_ifI _ _ (ConPanqueque.Front.sev_lower Γ _ (vv pVn) (i - d) vs.size hsub
    (by simp only [sev, sev_vv]; exact ha.gvn) (by omega) (by omega)) (fun h2 => ?_) (fun h2 => ?_)
  · have c2 : i - d < vs.size := by by_cases c2 : i - d < vs.size; exact c2; simp [bw, c2] at h2
    rw [dite_eq_left c2]
    have hv : C.H[ov + 1 + (vs.size - 1 - (i - d))]? = some (Enc.idxW vs[vs.size - 1 - (i - d)]) :=
      hcells _ (by omega)
    refine UD.specR_heapLoadI' (C := C) lA1 _ _ _ hv (by decide)
      (by
        simp only [sev, sev_vv, ha.gvs, ha.gvn, hb, ha.gdd]; simp
        rw [ExP.word_sub_eq i d (by omega) (by omega)]; exact ExP.addr_rev C ov vs.size i d c2 hsz) ?_
    refine specR_congr (m' := liftLooseBVarsFast n d 0 vs[vs.size - 1 - (i - d)] >>= fun r => pure r) (by simp) ?_
    refine ILP.callE_spec (C := C) (D := DI) (Γ := (lA1, Enc.idxW vs[vs.size - 1 - (i - d)]) :: Γ) lW ExL.fLiftF [pFu, ExL.pA, pD, pH] [.op .sub [vv pFu, .const 1], vv pD, .const 0, vv lA1]
      (ExL.fastBodyL C) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 0, Enc.idxW vs[vs.size - 1 - (i - d)]]
      (by decide) rfl (by decide) hc.liftF
      ⟨by simp only [sev, sev_vv, Env.get_cons, show pFu ≠ lA1 by decide, ite_false, ha.gfu]; simp; exact ofNat_succ_sub_one n,
        by simp only [sev, sev_vv, Env.get_cons, show pD ≠ lA1 by decide, ite_false, ha.gdd], rfl,
        by simp [sev, Env.get_cons], trivial⟩
      (ExL.fastL_spec ra C hok hc.cl s n d 0 _ (by omega) hd (by decide)) (fun r s1 => ?_)
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have c2 : ¬ i - d < vs.size := by intro c2; simp [bw, c2] at h2
    rw [dite_eq_right c2]
    refine specR_congr (m' := internBVarE (i - vs.size) >>= fun r => pure r) (by simp [internBVarE]) ?_
    refine specR_internBVarI ra hok hc.internBVar lW (.op .sub [vv lB, vv pVn]) (i - vs.size) (by omega) (by decide)
      (by simp only [sev, sev_vv, hb, ha.gvn]; simp; exact ExP.word_sub_eq i vs.size (by omega) (by omega)) (fun r s1 => ?_)
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem il_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ ilParams.zip vals).get x = none :=
  Knot.params_none C inst1Locals ilParams vals (by decide) (by decide)

theorem eqTag_sev (Γ : Env) (v : ENodeView) (k : Nat) (hk : k < 16) (hg : Γ.get lDg = some (BitVec.ofNat 64 v.tagN)) :
    sev Γ (eqTag k) = some (boolW (v.tagN == k)) := by
  have hv : v.tagN < 16 := by cases v <;> simp [ENodeView.tagN]
  exact ConPanqueque.T.WC.sev_eqNatB (by omega) (by omega) (by simp [sev, hg]) rfl

/-- **`instantiateLiftGo`**. -/
theorem il_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (hvs : VsAt C ov vs) : ∀ n, n < 2 ^ 63 → RecIL (σ := σ) C ov vs n := by
  intro n
  induction n with
  | zero =>
    intro _ h d s hd
    refine specR_prologue (postE_locals C) (il_none _ _) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sev, Env.get, ilParams, ctxEnv] at hw
  | succ n ih =>
    intro hf h d s hd
    have ih' := ih (by omega)
    refine specR_prologue (postE_locals C) (il_none _ _) ?_
    let Γ0 : Env := ctxEnv C ++ ilParams.zip [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 (n + 1), Enc.idxW h,
      BitVec.ofNat 64 d]
    have ha0 : ArmEnv C ov vs n h d Γ0 :=
      ⟨by simp +decide [Γ0, Env.get, ilParams, ctxEnv], by simp +decide [Γ0, Env.get, ilParams, ctxEnv],
        by simp +decide [Γ0, Env.get, ilParams, ctxEnv], by simp +decide [Γ0, Env.get, ilParams, ctxEnv],
        by simp +decide [Γ0, Env.get, ilParams, ctxEnv], by simp +decide [Γ0, Env.get, ilParams, ctxEnv]⟩
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) (by omega)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, ilParams, ctxEnv] at hw; exact absurd hw this
    rw [instantiateLiftGo_succ]
    refine specR_callNIM (C := C) lB ExB.fBvarB [pFu, pH] [.op .sub [vv pFu, .const 1], vv pH] (ExB.bvbBody C)
      [BitVec.ofNat 64 n, Enc.idxW h] (by decide) rfl (by decide) hc.bvb
      ⟨by have e : sev Γ0 (.op .sub [vv pFu, .const 1]) = some (BitVec.ofNat 64 n) := by
            simp only [sev, sev_vv, ha0.gfu]; simp; exact ofNat_succ_sub_one n
          exact e,
        by have e : sev Γ0 (vv pH) = some (Enc.idxW h) := by simp only [sev, sev_vv]; exact ha0.ghh
           exact e, trivial⟩
      (fun b w s' st => bvarB n h s = .ok (b, s') ∧ ExF.PostN C b w s' st) (fun _ _ _ _ hp => hp.2.2.2)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw; exact ExB.bvarB_spec C hok hc.cb s n h (by omega) _ (pre_of_lookups hu [pFu, pH] _ rfl hlk)))
      (fun b w s1 st ⟨hrun, hw, hb63, _⟩ => ?_)
    subst hw
    have ha1 := armEnv_cons ha0 lB (natW b) (by decide)
    refine specR_ifI _ _ (ConPanqueque.Front.sev_lower _ (vv pD) (vv lB) d b (by simp only [sev, sev_vv]; exact ha1.gdd)
      (by simp [sev, Env.get_cons, natW]) (by omega) (by omega)) (fun hlt => ?_) (fun hlt => ?_)
    swap
    · have c : ¬ d < b := by intro c; simp [bw, c] at hlt
      rw [if_pos (by omega)]
      exact specR_returnI _ _ (by simp only [sev, sev_vv]; exact ha1.ghh) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have c : d < b := by by_cases c : d < b; exact c; simp [bw, c] at hlt
    rw [if_neg (by omega)]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, ilParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact ha1.ghh) ?_
    refine ConPanqueque.T.Big.specR_viewP h (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, ilParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_runBind (show ConRon.Arena.view h s1 = .ok (v, s1) by rw [view_run, hv]) ?_
    have haV := armEnv_cons (armEnv_cons (armEnv_cons (armEnv_cons (armEnv_cons (armEnv_cons (armEnv_cons ha1 lFl C.FLe
      (by decide)) lDh (Enc.idxW h) (by decide)) lDi (BitVec.ofNat 64 h.idxNat) (by decide)) lDg (BitVec.ofNat 64 v.tagN)
      (by decide)) lDt (BitVec.ofNat 64 h.tier.toNat) (by decide)) lRn (BitVec.ofNat 64 (encEView v).length) (by decide))
      lRp P (by decide)
    have hg : ∀ k, k < 16 → sev ((lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) ::
        (lDt, BitVec.ofNat 64 h.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lB, natW b) :: Γ0) (eqTag k) = some (boolW (v.tagN == k)) :=
      fun k hk => eqTag_sev _ v k hk (by simp +decide [Env.get_cons])
    have hpP : ∀ (Γ : Env), Γ = (lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) ::
        (lDt, BitVec.ofNat 64 h.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) ::
        (lDh, Enc.idxW h) :: (lFl, C.FLe) :: (lB, natW b) :: Γ0 → Γ.get lRp = some P := fun Γ e => by subst e; simp
    have no : ∀ k, (v.tagN == k) = false → boolW (v.tagN == k) = 0 := fun k e => by simp [e, boolW]
    have yes : ∀ k, (v.tagN == k) = true → boolW (v.tagN == k) ≠ 0 := fun k e => by simp [e, boolW]
    cases v with
    | bvar i =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 0 rfl))
      unfold bvarArmIL
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, Enc.limbs,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact bvarRestIL_spec ra C hok hc ov vs hvs n (by omega) h d hd 0 (by decide)
          (armEnv_cons haV lB 0 (by decide)) (by simp [Env.get_cons])
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by decide)
            (by simp +decide [sev, Env.get_cons]) rfl
            (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this) ?_
          exact bvarRestIL_spec ra C hok hc ov vs hvs n (by omega) h d hd i ib
            (armEnv_cons haV lB _ (by decide)) (by simp [Env.get_cons])
        · have hl := limbs_len_ge2 i (by omega)
          have hlt' : (Enc.limbs i).length < 2 ^ 61 := hlen
          have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hn0,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, encEView, Enc.encBVar, hn1,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    | app f a =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 4 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 4 rfl))
      exact appArmIL_spec ra C hok hc ov vs n ih' h d hd f a P haV (by simp [Env.get_cons])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW a] [])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem1 P (Enc.idxW f) (Enc.idxW a) [] [])
    | lam ty bd =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 5 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 5 rfl))
      exact lamArmIL_spec ra C hok hc ov vs n ih' h d hd ty bd P haV (by simp [Env.get_cons])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW bd] [])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW bd) [] [])
    | forallE ty bd =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 6 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 6 rfl))
      exact forallEArmIL_spec ra C hok hc ov vs n ih' h d hd ty bd P haV (by simp [Env.get_cons])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW bd] [])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW bd) [] [])
    | letE ty val bd =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 7 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 7 rfl))
      exact letArmIL_spec ra C hok hc ov vs n ih' h d hd ty val bd P haV (by simp [Env.get_cons])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW val, Enc.idxW bd] [])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW val) [Enc.idxW bd] [])
        (by simpa [encEView, Enc.encApp, Enc.encBind, Enc.encLet] using wordsAt_get P [Enc.idxW ty, Enc.idxW val, Enc.idxW bd] 2 (by simp) [])
    | proj c i sub =>
      refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
      refine specR_ifI _ _ (hg 9 (by decide)) (fun _ => ?_) (fun hw => absurd hw (yes 9 rfl))
      unfold projArmIL
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P (Enc.idxW c) (Enc.idxW sub :: Enc.limbs i) []) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev, Env.get_cons])
        rfl (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW sub) (Enc.limbs i) []) ?_
      have haP := armEnv_cons (armEnv_cons haV lA1 (Enc.idxW c) (by decide)) lA2 (Enc.idxW sub) (by decide)
      have hlenP : (encEView (.proj c i sub)).length = 2 + (Enc.limbs i).length := by
        simp [encEView, Enc.encProj]; omega
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenP, Enc.limbs,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact projRestIL_spec ra C hok hc ov vs n ih' h d hd c 0 sub (by decide) (armEnv_cons haP lB 0 (by decide))
          (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenP, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlenP, hl,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) (by decide)
            (by simp +decide [sev, Env.get_cons]) rfl
            (by simpa [encEView, Enc.encProj, hl] using
              wordsAt_get P [Enc.idxW c, Enc.idxW sub, BitVec.ofNat 64 i] 2 (by simp) []) ?_
          exact projRestIL_spec ra C hok hc ov vs n ih' h d hd c i sub ib (armEnv_cons haP lB _ (by decide))
            (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
        · have hl := limbs_len_ge2 i (by omega)
          have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenP, hn2,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlenP, hn3,
              Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    | fvar _ _ | sort _ | const _ _ | lit _ =>
      all_goals
        refine specR_ifI _ _ (hg 0 (by decide)) (fun hw => absurd (no 0 rfl) hw) (fun _ => ?_)
        refine specR_ifI _ _ (hg 4 (by decide)) (fun hw => absurd (no 4 rfl) hw) (fun _ => ?_)
        refine specR_ifI _ _ (hg 5 (by decide)) (fun hw => absurd (no 5 rfl) hw) (fun _ => ?_)
        refine specR_ifI _ _ (hg 6 (by decide)) (fun hw => absurd (no 6 rfl) hw) (fun _ => ?_)
        refine specR_ifI _ _ (hg 7 (by decide)) (fun hw => absurd (no 7 rfl) hw) (fun _ => ?_)
        refine specR_ifI _ _ (hg 9 (by decide)) (fun hw => absurd (no 9 rfl) hw) (fun _ => ?_)
        exact specR_returnI _ _ (by simp only [sev, sev_vv]; exact haV.ghh) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

theorem inst1LClear_run (s : AState) :
    inst1LClear s = .ok ((), { s with memos := memoUpd .inst1L s.memos ∅ }) := rfl

def fInstLF := ofString "instantiateLift"

def fastBodyIL (C : Ctx) : ProgHOL 64 :=
  prologue fastLocals (clearCode (C.mg (.e .inst1L))
    (.seq (.call (some (some (.local, lW), none)) fInstL [vv pVs, vv pVn, vv pFu, vv pH, vv pD])
      (clearCode (C.mg (.e .inst1L)) (.return (vv lW)))))

section
variable {σ : Type}

/-- **`instantiateLiftFast`**: the memo fresh before the walk and dropped after. -/
theorem fastIL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesIL C)
    (ov : Nat) (vs : Array EIdx) (hvs : VsAt C ov vs) (s : AState) (fuel : Nat) (e : EIdx) (d : Nat)
    (hf : fuel < 2 ^ 63) (hd : d < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s (ilParams.zip [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 fuel, Enc.idxW e,
      BitVec.ofNat 64 d])) (fastBodyIL C) s (instantiateLiftFast fuel e vs d) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fastLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  unfold instantiateLiftFast
  refine specR_memoClearI hok .inst1L inst1LClear inst1LClear_run (by decide) ?_
  refine ILP.callE_spec lW fInstL ilParams [vv pVs, vv pVn, vv pFu, vv pH, vv pD] (bodyIL C)
    [cellA C ov, BitVec.ofNat 64 vs.size, BitVec.ofNat 64 fuel, Enc.idxW e, BitVec.ofNat 64 d] (by decide) rfl
    (by decide) hc.il
    ⟨by simp +decide [Env.kill, Env.get, ilParams, ctxEnv], by simp +decide [Env.kill, Env.get, ilParams, ctxEnv],
      by simp +decide [Env.kill, Env.get, ilParams, ctxEnv], by simp +decide [Env.kill, Env.get, ilParams, ctxEnv],
      by simp +decide [Env.kill, Env.get, ilParams, ctxEnv], trivial⟩
    (il_spec ra C hok hc ov vs hvs fuel hf e d _ hd) (fun r s' => ?_)
  refine specR_memoClearI hok .inst1L inst1LClear inst1LClear_run (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExIL
