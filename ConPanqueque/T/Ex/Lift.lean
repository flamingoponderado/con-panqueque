import ConPanqueque.T.Ex.Inst1Fast
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `liftLooseBVarsGo`

Lift loose `bvar`s at or above the cutoff `c` by `amount`: the derived-word cutoff, the full view,
and memoized arms (memo `liftC`). As a Pancake function `lift(am, fu, h, c)`.
-/

namespace ConPanqueque.T.ExL
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI

def fLift := ofString "liftGo"
def pA := ofString "am"

def callL (x arg : MlS) (cE : ExpHOL 64) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fLift [vv pA, .op .sub [vv pFu, .const 1], vv arg, cE]

def tagEq (k : Nat) : ExpHOL 64 := .cmp .equal (vv lDg) (.const (BitVec.ofNat 64 k))

/-- Two children at `rp`, `rp + 8`, both at cutoff `c`, rebuilt by `fn`. -/
def appL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (probed G (.seq (callL lY lA1 (vv pD)) (.seq (callL lZ lA2 (vv pD))
    (.seq (.call (some (some (.local, lW), none)) fInternApp [vv lY, vv lZ]) (memoSetP G (.return (vv lW))))))))

/-- A binder: type at `c`, body at `c + 1`. -/
def bindL (G : BitVec 64) (fn : MlS) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (probed G (.seq (.assign .local lD1 (.op .add [vv pD, .const 1])) (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callL lY lA1 (vv pD)) (.seq (callL lZ lA2 (vv lD1))
      (.seq (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ]) (memoSetP G (.return (vv lW))))))))))

def letL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
  (probed G (.seq (.assign .local lD1 (.op .add [vv pD, .const 1])) (.ite (.shift .lsr (vv lD1) (.const 63)) hang
    (.seq (callL lY lA1 (vv pD)) (.seq (callL lZ lA2 (vv pD)) (.seq (callL lB lA3 (vv lD1))
      (.seq (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB])
        (memoSetP G (.return (vv lW))))))))))))

/-- `proj`: the index word already in `bb` (guarded), the sub-term at `rp + 8`. -/
def projRestL (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (probed G (.seq (callL lY lA2 (vv pD))
      (.seq (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (memoSetP G (.return (vv lW))))))

def projL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestL G))
    (.ite (.cmp .equal (vv lRn) (.const 3))
      (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestL G)) hang)))

/-- `bvar i`: `i ≥ c` interns `bvar (i + amount)` (guarded below `2^63`), else `h`. -/
def bvarRestL : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
    (.ite (.cmp .lower (vv lB) (vv pD)) (.return (vv pH))
      (.seq (.assign .local lW (.op .add [vv lB, vv pA]))
        (.ite (.shift .lsr (vv lW) (.const 63)) hang
          (.seq (.call (some (some (.local, lW), none)) fInternBVar [vv lW]) (.return (vv lW))))))

def bvarL : ProgHOL 64 :=
  .ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local lB (.const 0)) bvarRestL)
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 0])))
      bvarRestL) hang)

def coreL (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
   (.seq (.assign .local lB (bvarFieldE (vv lDo1)))
   (.ite (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)]) (.return (vv pH))
    (.seq eViewP
     (.ite (tagEq 4) (appL G)
      (.ite (tagEq 5) (bindL G fInternLam)
       (.ite (tagEq 6) (bindL G fInternForallE)
        (.ite (tagEq 7) (letL G)
         (.ite (tagEq 9) (projL G)
          (.ite (tagEq 0) bvarL (.return (vv pH))))))))))))))

def bodyL (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreL (C.mG (.e .lift)))

theorem liftGet_run (k : EIdx × Nat) (s : AState) : liftGet k s = .ok ((memoSel .lift s.memos)[k]?, s) := rfl
theorem liftSet_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    liftSet k r s = .ok ((), { s with memos := memoUpd .lift s.memos ((memoSel .lift s.memos).insert k r) }) := rfl

structure CodesL (C : Ctx) (B : ProgHOL 64) : Prop where
  lift : C.code.lookup fLift = some ([(pA, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one)
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

section
variable {σ : Type}

def RecL (C : Ctx) (B : ProgHOL 64) (n : Nat) : Prop :=
  ∀ (am : Nat) (h : EIdx) (c : Nat) (s : AState), am < 2 ^ 63 → c < 2 ^ 63 →
    SpecR (Pre (σ := σ) C s [(pA, BitVec.ofNat 64 am), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 c)]) B s (liftLooseBVarsGo am n h c) (PostE C)

theorem callL_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fLift = some ([(pA, .one), (pFu, .one), (pH, .one), (pD, .one)], B, .one))
    (n : Nat) (ih : RecL (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x arg : MlS) (cE : ExpHOL 64) (am : Nat) (h : EIdx) (c : Nat)
    (ham : am < 2 ^ 63) (hc : c < 2 ^ 63) (hx : x ∈ DI)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (harg : Γ.get arg = some (Enc.idxW h)) (hcE : sev Γ cE = some (BitVec.ofNat 64 c))
    (hk : ∀ a s', SpecR (Inv C s' ((x, Enc.idxW a) :: Γ) [] DI) rest s' (k a) R) :
    SpecR (Inv C s Γ M DI) (.seq (callL x arg cE) rest) s (liftLooseBVarsGo am n h c >>= k) R := by
  refine specR_call4IM x fLift pA pFu pH pD (by decide) _ _ _ _ B (BitVec.ofNat 64 am) (BitVec.ofNat 64 (n + 1) - 1)
    (Enc.idxW h) (BitVec.ofNat 64 c) hx hcode (by simp [hA]) (by simp [sev, hfu]) (by simp [harg]) hcE
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact ih am h c s ham hc _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; rw [h2, ofNat_succ_sub_one]
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · simp at hy⟩)
    (fun a w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk a s')

/-- The memo probe in front of an arm: a hit answers, a miss runs `miss`. -/
theorem probedL_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesL C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (c : Nat) (hc63 : c < 2 ^ 63) (miss : ProgHOL 64) (m : AM EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) C s ((lX, 0) :: Γ) [] DI) miss s m (PostE C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (probed (C.mG (.e .lift)) miss) s
      (do match ← liftGet (h, c) with | some r => pure r | none => m) (PostE C) := by
  unfold probed memoGetP
  refine specR_memoGetI hok .lift liftGet liftGet_run hc.memoGet hc.memoProbe lX (vv pH) (vv pD) h c hc63 (by decide)
    (by simp [hh]) (by simp [hcc]) hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW, optWG]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    exact specR_ifI (vv lX) 0 (by simp [optW, optWG]) (fun hw => absurd rfl hw) (fun _ => hmiss)

/-- `KB[0..1] := (h, c); memoSet(liftC, w); return w`. -/
theorem setRetL_spec {C : Ctx} (hok : CtxOK C) (B : ProgHOL 64) (hc : CodesL C B) {s : AState} {Γ : Env}
    {M : Mem} (h : EIdx) (c : Nat) (hc63 : c < 2 ^ 63) (r : EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hkb : Γ.get lKb = some C.KB)
    (hw : Γ.get lW = some (Enc.idxW r)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (memoSetP (C.mG (.e .lift)) (.return (vv lW))) s
      (do liftSet (h, c) r; pure r) (PostE C) := by
  unfold memoSetP
  refine specR_memoSetI hok .lift liftSet liftSet_run hc.memoSet hc.memoIns lX (vv pH) (vv pD) (vv lW) h c r hc63
    (by decide) (by simp [hh]) (by simp [hcc]) (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [hw]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem appL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesL C B) (n : Nat) (ih : RecL (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (am : Nat) (h : EIdx) (c : Nat) (ham : am < 2 ^ 63) (hc63 : c < 2 ^ 63) (P : BitVec 64)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (a b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW a) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (appL (C.mG (.e .lift))) s (liftArmApp am n h c a b) (PostE C) := by
  unfold appL
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW a) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_congr (by rw [liftArmApp]) ?_
  refine probedL_spec hok B hc h c hc63 _ _ (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb]) ?_
  refine callL_spec C B hc.lift n ih lY lA1 (vv pD) am a c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun a' s1 => ?_)
  refine callL_spec C B hc.lift n ih lZ lA2 (vv pD) am b c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun b' s2 => ?_)
  refine specR_internAppI ra hok hc.internApp lW (vv lY) (vv lZ) a' b' (by decide) (by simp +decide)
    (by simp +decide) (fun r s3 => ?_)
  exact setRetL_spec hok B hc h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
    (by simp +decide)

theorem bindL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesL C B) (n : Nat) (ih : RecL (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (am : Nat) (h : EIdx) (c : Nat) (ham : am < 2 ^ 63) (hc63 : c < 2 ^ 63) (P : BitVec 64)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (ty b : EIdx) (fn : MlS) (op : EIdx → EIdx → AM EIdx)
    (hop : ∀ {β : Type} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {k : EIdx → AM β}
      {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (t b : EIdx), x ∈ DI →
      sev Γ e1 = some (Enc.idxW t) → sev Γ e2 = some (Enc.idxW b) →
      (∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] DI) rest s' (k h) R) →
      SpecR (Inv C s Γ M DI) (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest) s (op t b >>= k) R)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (bindL (C.mG (.e .lift)) fn) s
      (do match ← liftGet (h, c) with
        | some r => pure r
        | none => do
          let t ← liftLooseBVarsGo am n ty c
          let b' ← liftLooseBVarsGo am n b (c + 1)
          let r ← op t b'
          liftSet (h, c) r
          pure r) (PostE C) := by
  unfold bindL
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW ty) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine probedL_spec hok B hc h c hc63 _ _ (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb]) ?_
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (c + 1)) (by decide) (by simp +decide [sev, hcc]; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (c + 1) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero (c + 1) (by omega)).mp hw
  refine callL_spec C B hc.lift n ih lY lA1 (vv pD) am ty c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
  refine callL_spec C B hc.lift n ih lZ lA2 (vv lD1) am b (c + 1) ham hlt (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s2 => ?_)
  refine hop lW (vv lY) (vv lZ) t' b' (by decide) (by simp +decide) (by simp +decide) (fun r s3 => ?_)
  exact setRetL_spec hok B hc h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
    (by simp +decide)

theorem letL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesL C B) (n : Nat) (ih : RecL (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (am : Nat) (h : EIdx) (c : Nat) (ham : am < 2 ^ 63) (hc63 : c < 2 ^ 63) (P : BitVec 64)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (hrp : Γ.get lRp = some P) (ty v b : EIdx)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW v) ∈ M)
    (hm2 : (P + BitVec.ofNat 64 16, Enc.idxW b) ∈ M) :
    SpecR (Inv (σ := σ) C s Γ M DI) (letL (C.mG (.e .lift))) s (liftArmLet am n h c ty v b) (PostE C) := by
  unfold letL
  refine specR_loadI' lA1 _ (P + 0) _ (Enc.idxW ty) (by decide) (by simp [sev, hrp]) rfl hm0 ?_
  refine specR_loadI' lA2 _ (P + 8) _ (Enc.idxW v) (by decide) (by simp +decide [sev, hrp]) rfl hm1 ?_
  refine specR_loadI' lA3 _ (P + 16) _ (Enc.idxW b) (by decide) (by simp +decide [sev, hrp]) rfl hm2 ?_
  refine specR_congr (by rw [liftArmLet]) ?_
  refine probedL_spec hok B hc h c hc63 _ _ (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb]) ?_
  refine specR_assignI lD1 _ (BitVec.ofNat 64 (c + 1)) (by decide) (by simp +decide [sev, hcc]; rw [word_add1_eq]) ?_
  refine specR_ifI (.shift .lsr (vv lD1) (.const 63)) (BitVec.ofNat 64 (c + 1) >>> (63 : BitVec 64).toNat)
    (by simp +decide [sev]) (fun _ => specR_hangI) (fun hw => ?_)
  have hlt := (shr63_eq_zero (c + 1) (by omega)).mp hw
  refine callL_spec C B hc.lift n ih lY lA1 (vv pD) am ty c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun t' s1 => ?_)
  refine callL_spec C B hc.lift n ih lZ lA2 (vv pD) am v c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide [hcc]) (fun v' s2 => ?_)
  refine callL_spec C B hc.lift n ih lB lA3 (vv lD1) am b (c + 1) ham hlt (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide) (by simp +decide) (fun b' s3 => ?_)
  refine specR_internLetI ra hok hc.internLet lW (vv lY) (vv lZ) (vv lB) t' v' b' (by decide) (by simp +decide)
    (by simp +decide) (by simp +decide) (fun r s4 => ?_)
  exact setRetL_spec hok B hc h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
    (by simp +decide)

end

section
variable {σ : Type}

theorem projRestL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesL C B) (n : Nat) (ih : RecL (σ := σ) C B n) {s : AState} {Γ : Env} {M : Mem}
    (am : Nat) (h : EIdx) (c : Nat) (ham : am < 2 ^ 63) (hc63 : c < 2 ^ 63) (nm : NIdx) (i : Nat) (sub : EIdx)
    (hi : i < 2 ^ 64)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hcc : Γ.get pD = some (BitVec.ofNat 64 c))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW sub))
    (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) (projRestL (C.mG (.e .lift))) s (liftArmProj am n h c nm i sub) (PostE C) := by
  unfold projRestL
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine specR_congr (by rw [liftArmProj]) ?_
  refine probedL_spec hok B hc h c hc63 _ _ hh hcc hkb ?_
  refine callL_spec C B hc.lift n ih lY lA2 (vv pD) am sub c ham hc63 (by decide) (by simp +decide [hA])
    (by simp +decide [hfu]) (by simp +decide [ha2]) (by simp +decide [hcc]) (fun u s1 => ?_)
  refine specR_internProjI ra hok hc.internProj lW (vv lA1) (vv lY) (vv lB) nm i u hi63 (by decide)
    (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hb]) (fun r s2 => ?_)
  exact setRetL_spec hok B hc h c hc63 r (by simp +decide [hh]) (by simp +decide [hcc]) (by simp +decide [hkb])
    (by simp +decide)

theorem bvarRestL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesL C B) {s : AState} {Γ : Env} {M : Mem} (am : Nat) (h : EIdx) (c i : Nat) (ham : am < 2 ^ 63)
    (hc63 : c < 2 ^ 63) (hi : i < 2 ^ 64)
    (hA : Γ.get pA = some (BitVec.ofNat 64 am)) (hh : Γ.get pH = some (Enc.idxW h))
    (hcc : Γ.get pD = some (BitVec.ofNat 64 c)) (hb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) C s Γ M DI) bvarRestL s
      (if i ≥ c then internE (.bvar (i + am)) else pure h) (PostE C) := by
  unfold bvarRestL
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  by_cases g : i < c
  · have hlt : BitVec.ofNat 64 i < BitVec.ofNat 64 c := (word_lt_iff i c hi (by omega)).mpr g
    refine specR_ifI _ 1 (by simp [sev, hb, hcc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure h) (by simp [show ¬ i ≥ c by omega]) ?_
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp [hh]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hnlt : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 c := fun x => g ((word_lt_iff i c hi (by omega)).mp x)
    refine specR_ifI _ 0 (by simp [sev, hb, hcc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt])
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_assignI lW _ (BitVec.ofNat 64 (i + am)) (by decide)
      (by simp +decide [sev, hb, hA]; rw [BitVec.ofNat_add_ofNat]) ?_
    refine specR_ifI (.shift .lsr (vv lW) (.const 63)) (BitVec.ofNat 64 (i + am) >>> (63 : BitVec 64).toNat)
      (by simp [sev]) (fun _ => specR_hangI) (fun hw2 => ?_)
    have hs63 := (shr63_eq_zero (i + am) (by omega)).mp hw2
    refine specR_congr (m' := internBVarE (i + am) >>= fun a => pure a) (by simp [show i ≥ c by omega]; rfl) ?_
    refine specR_internBVarI ra hok hc.internBVar lW (vv lW) (i + am) hs63 (by decide) (by simp) (fun r s' => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem params_noneL (am : Nat) (h : EIdx) (n c : Nat) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pA, BitVec.ofNat 64 am), (pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h),
      (pD, BitVec.ofNat 64 c)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem liftGo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesL C (bodyL C)) :
    ∀ n, n < 2 ^ 64 → RecL (σ := σ) C (bodyL C) n := by
  intro n
  induction n with
  | zero =>
    intro _ am h c s _ _
    refine specR_prologue (postE_locals C) (params_noneL am h 0 c C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf am h c s ham hc63
    have ih' := ih (by omega)
    refine specR_prologue (postE_locals C) (params_noneL am h (n + 1) c C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    refine specR_congr (by rw [liftLooseBVarsGo_succ]) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) rfl ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) rfl ?_
    refine specR_derivedEI h rfl rfl rfl (by decide) ?_
    have hbt : (ConLeche.bvarOfData (s.store.derived h)).toBitVec =
        BitVec.ofNat 64 (ConLeche.bvarOfData (s.store.derived h)).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    have hb15 : (ConLeche.bvarOfData (s.store.derived h)).toNat < 2 ^ 15 := by
      simp only [ConLeche.bvarOfData, UInt64.toNat_mod]; simp; omega
    refine specR_assignI lB (bvarFieldE (vv lDo1)) (ConLeche.bvarOfData (s.store.derived h)).toBitVec (by decide)
      (by simp [sev, bvarFieldE]; exact bvarOfData_word _) ?_
    generalize hbdef : (ConLeche.bvarOfData (s.store.derived h)).toNat = b at hb15 hbt
    refine specR_iteI (.op .and [.cmp .lower (vv lB) (.const 32767), .cmp .notLower (vv pD) (vv lB)])
      ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 b) 32767 then (1 : BitVec 64) else 0) &&&
        (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notLower (BitVec.ofNat 64 c) (BitVec.ofNat 64 b) then 1 else 0))
      ?_ (cutoff_iff b c hb15 hc63) (fun _ => ?_) (fun _ => ?_)
    · simp +decide [sev, Env.kill, ctxEnv, hbt]
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_viewI h (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by decide) (fun v P htg hsh => ?_)
    cases v with
    | bvar i =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact bvarRestL_spec ra C hok (bodyL C) hc am h c 0 ham hc63 (by decide) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp)
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, encEView, Enc.encBVar, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) (by decide) (by simp +decide [sev])
            rfl (by have := wordsAt_mem0 P (BitVec.ofNat 64 i) [] (M := []); simpa [encEView, Enc.encBVar, hl] using this)
            ?_
          exact bvarRestL_spec ra C hok (bodyL C) hc am h c i ham hc63 ib (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp)
        · have hl := limbs_len_ge2 i (by omega)
          have hlt : (Enc.limbs i).length < 2 ^ 61 := hsh
          have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp +decide [sev, encEView, Enc.encBVar, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => specR_hangI)
    | fvar idx ty =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | sort u =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | const nm us =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | lit l =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [Env.kill, ctxEnv]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | app a b =>
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      refine appL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 P ?_ ?_ ?_ ?_ ?_ ?_ a b
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [Env.kill, ctxEnv]
    | lam ty bd =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      refine specR_congr (m' := liftArmLam am n h c ty bd) rfl ?_
      refine specR_congr (by rw [liftArmLam]) ?_
      refine bindL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 P ?_ ?_ ?_ ?_ ?_ ?_ ty bd fInternLam
        internLamE (fun x e1 e2 t b hx h1 h2 hk => specR_internLamI ra hok hc.internLam x e1 e2 t b hx h1 h2 hk)
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [Env.kill, ctxEnv]
    | forallE ty bd =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      refine specR_congr (m' := liftArmForallE am n h c ty bd) rfl ?_
      refine specR_congr (by rw [liftArmForallE]) ?_
      refine bindL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 P ?_ ?_ ?_ ?_ ?_ ?_ ty bd fInternForallE
        internForallEE (fun x e1 e2 t b hx h1 h2 hk => specR_internForallEI ra hok hc.internForallE x e1 e2 t b hx h1 h2 hk)
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) <;> simp +decide [Env.kill, ctxEnv]
    | letE ty vl bd =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      refine letL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 P ?_ ?_ ?_ ?_ ?_ ?_ ty vl bd
        (wordsAt_mem0 _ _ _ _) (wordsAt_mem1 _ _ _ _ _) (wordsAt_mem2 _ _ _ _ _ _) <;> simp +decide [Env.kill, ctxEnv]
    | proj nm i sub =>
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw) (fun _ => ?_)
      refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => by simp [ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw)
      unfold projL
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
        (wordsAt_mem1 _ _ _ _ _) ?_
      have hlen : (encEView (.proj nm i sub)).length = 2 + (Enc.limbs i).length := by
        simp [encEView, Enc.encProj]; omega
      by_cases i0 : i = 0
      · subst i0
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
        exact projRestL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 nm 0 sub (by decide) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
          (by simp +decide) (by simp +decide) (by simp)
      · by_cases ib : i < 2 ^ 64
        · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
          refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun hw => absurd hw (by decide))
          refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
            (by simp +decide [sev]) rfl
            (by have := wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW sub) (BitVec.ofNat 64 i) [] (M := [])
                simpa [encEView, Enc.encProj, hl] using this) ?_
          exact projRestL_spec ra C hok (bodyL C) hc n ih' am h c ham hc63 nm i sub ib (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
            (by simp +decide) (by simp +decide) (by simp)
        · have hl := limbs_len_ge2 i (by omega)
          have hlt : 2 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen]; exact hsh
          have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
            intro e; have := congrArg BitVec.toNat e; simp at this; omega
          refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun hw => absurd rfl hw) (fun _ => specR_hangI)

end

theorem liftClear_run (s : AState) : liftClear s = .ok ((), { s with memos := memoUpd .lift s.memos ∅ }) := rfl

def fLiftF := ofString "liftLooseBVars"

def fastBodyL (C : Ctx) : ProgHOL 64 :=
  prologue fastLocals (clearCode (C.mg (.e .lift))
    (.seq (.call (some (some (.local, lW), none)) fLift [vv pA, vv pFu, vv pH, vv pD])
      (clearCode (C.mg (.e .lift)) (.return (vv lW)))))

section
variable {σ : Type}

theorem fastL_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesL C (bodyL C))
    (s : AState) (fuel am c : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (ham : am < 2 ^ 63) (hc63 : c < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pA, BitVec.ofNat 64 am), (pD, BitVec.ofNat 64 c),
      (pH, Enc.idxW e)]) (fastBodyL C) s (liftLooseBVarsFast fuel am c e) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [fastLocals, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  refine specR_memoClearI hok .lift liftClear liftClear_run (by decide) ?_
  refine specR_call4IM lW fLift pA pFu pH pD (by decide) _ _ _ _ (bodyL C) (BitVec.ofNat 64 am)
    (BitVec.ofNat 64 fuel) (Enc.idxW e) (BitVec.ofNat 64 c) (by decide) hc.lift (by simp +decide [Env.kill, ctxEnv])
    (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv]) (by simp +decide [Env.kill, ctxEnv])
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 h4 w hw => by
      subst hw
      exact liftGo_spec ra C hok hc fuel hf am e c _ ham hc63 _ ⟨hu, fun y z hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · split at hy
              · rename_i e; subst e; simp at hy; subst hy; exact h4
              · simp at hy⟩)
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, _⟩ := hp
  refine specR_memoClearI hok .lift liftClear liftClear_run (by decide) ?_
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [Env.kill])
    (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExL
